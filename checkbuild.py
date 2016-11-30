#!/usr/bin/env python
#
# Copyright (C) 2015 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
"""Verifies that the build is sane.

Cleans old build artifacts, configures the required environment, determines
build goals, and invokes the build scripts.
"""
from __future__ import absolute_import
from __future__ import print_function

import argparse
import collections
import inspect
import itertools
import multiprocessing
import os
import shutil
import site
import subprocess
import sys
import tempfile
import textwrap
import traceback

import config
import build.lib.build_support as build_support
import ndk.workqueue


ALL_MODULES = {
    'clang',
    'cpufeatures',
    'gabi++',
    'gcc',
    'gdbserver',
    'gnustl',
    'gtest',
    'host-tools',
    'libandroid_support',
    'libc++',
    'libc++abi',
    'libshaderc',
    'native_app_glue',
    'ndk-build',
    'ndk_helper',
    'platforms',
    'python-packages',
    'shader_tools',
    'simpleperf',
    'stlport',
    'sysroot',
    'system-stl',
    'vulkan',
}


class ArgParser(argparse.ArgumentParser):
    def __init__(self):
        super(ArgParser, self).__init__(
            description=inspect.getdoc(sys.modules[__name__]))

        self.add_argument(
            '--arch',
            choices=('arm', 'arm64', 'mips', 'mips64', 'x86', 'x86_64'),
            help='Build for the given architecture. Build all by default.')
        self.add_argument(
            '-j', '--jobs', type=int, default=multiprocessing.cpu_count(),
            help=('Number of parallel builds to run. Note that this will not '
                  'affect the -j used for make; this just parallelizes '
                  'checkbuild.py. Defaults to the number of CPUs available.'))

        package_group = self.add_mutually_exclusive_group()
        package_group.add_argument(
            '--package', action='store_true', dest='package', default=True,
            help='Package the NDK when done building (default).')
        package_group.add_argument(
            '--no-package', action='store_false', dest='package',
            help='Do not package the NDK when done building.')
        package_group.add_argument(
            '--force-package', action='store_true', dest='force_package',
            help='Force a package even if only building a subset of modules.')

        test_group = self.add_mutually_exclusive_group()
        test_group.add_argument(
            '--test', action='store_true', dest='test', default=True,
            help=textwrap.dedent("""\
            Run host tests when finished. --package is required. Not supported
            when targeting Windows.
            """))
        test_group.add_argument(
            '--no-test', action='store_false', dest='test',
            help='Do not run host tests when finished.')

        self.add_argument(
            '--build-number', help='Build number for use in version files.')
        self.add_argument(
            '--release', help='Ignored. Temporarily compatibility.')

        self.add_argument(
            '--system', choices=('darwin', 'linux', 'windows', 'windows64'),
            default=build_support.get_default_host(),
            help='Build for the given OS.')

        module_group = self.add_mutually_exclusive_group()

        module_group.add_argument(
            '--module', choices=sorted(ALL_MODULES),
            help='NDK modules to build.')

        module_group.add_argument(
            '--host-only', action='store_true',
            help='Skip building target components.')


def _invoke_build(script, args):
    if args is None:
        args = []
    subprocess.check_call([build_support.android_path(script)] + args)


def invoke_build(script, args=None):
    script_path = os.path.join('build/tools', script)
    _invoke_build(build_support.ndk_path(script_path), args)


def invoke_external_build(script, args=None):
    _invoke_build(build_support.android_path(script), args)


def package_ndk(out_dir, dist_dir, args):
    package_args = common_build_args(out_dir, dist_dir, args)
    package_args.append(dist_dir)

    if args.build_number is not None:
        package_args.append('--build-number={}'.format(args.build_number))

    if args.arch is not None:
        package_args.append('--arch={}'.format(args.arch))

    invoke_build('package.py', package_args)


def group_by_test(details):
    """Arranges per-ABI test results into failures by name.

    Args:
        details: dict of {abi: {suite_name: [results]}}.

    Returns:
        Dict of {test_name: (abi, result)}.
    """
    by_test = {}
    for abi, suites in details.iteritems():
        for suite, test_results in suites.iteritems():
            for test in test_results:
                if test.failed():
                    name = '.'.join([suite, test.test_name])
                    if name not in by_test:
                        by_test[name] = []
                    by_test[name].append((abi, test))
    return by_test


def make_test_report(details, use_color):
    """Returns a string containing a test failure report.

    Args:
        details: dict of {abi: suite_name: [results]}}.
        use_color: Print results with color if True.

    Returns:
        Test failure report as a string.
    """
    grouped_details = group_by_test(details)
    lines = []
    for test_name, test_failures in grouped_details.iteritems():
        lines.append('BEGIN TEST RESULT: ' + test_name)
        lines.append('=' * 80)
        for abi, result in test_failures:
            lines.append('FAILED {}'.format(abi))
            lines.append(result.to_string(colored=use_color))
    return os.linesep.join(lines)


def test_ndk(out_dir, dist_dir, args):
    """Runs the host-only tests on the just built NDK.

    Only runs the tests for Clang due to resource constraints.

    Args:
        out_dir: Build output directory.
        dist_dir: Preserved artifact directory.
        args: Parsed command line arguments.

    Returns:
        True if all tests pass, else False.
    """
    # The packaging step extracts all the modules to a known directory for
    # packaging. This directory is not cleaned up after packaging, so we can
    # reuse that for testing.
    test_dir = os.path.join(out_dir, 'android-ndk-{}'.format(config.release))

    test_env = dict(os.environ)
    test_env['NDK'] = test_dir

    abis = build_support.ALL_ABIS
    if args.arch is not None:
        abis = build_support.arch_to_abis(args.arch)

    use_color = sys.stdin.isatty() and os.name != 'nt'
    results = collections.OrderedDict()

    site.addsitedir(os.path.join(test_dir, 'python-packages'))
    import tests.runners
    import tests.printers

    configurations = itertools.product(
        abis,
        ['clang'],  # Toolchains to test. Don't bother with GCC.
        [False, True],  # Force unified headers.
    )

    details = {}
    for abi, toolchain, force_unified_headers in configurations:
        if force_unified_headers:
            force_unified_headers_str = 'unified headers'
        else:
            force_unified_headers_str = 'legacy headers'

        cfg = ' '.join([abi, toolchain, force_unified_headers_str])
        test_out_dir = os.path.join(out_dir, 'test', abi)
        results[cfg], details[cfg] = tests.runners.run_single_configuration(
            test_dir, test_out_dir,
            tests.printers.StdoutPrinter(use_color=use_color),
            abi, toolchain, skip_run=True,
            force_unified_headers=force_unified_headers)

    all_pass = all(results.values())
    if not all_pass:
        test_report = make_test_report(details, use_color)
        print(test_report)
        log_path = os.path.join(dist_dir, 'logs/build_error.log')
        with open(log_path, 'a') as error_log:
            error_log.write(test_report)

    print('Results:')
    for abi, result in results.iteritems():
        print('{}: {}'.format(abi, 'PASS' if result else 'FAIL'))
    return all_pass


def common_build_args(out_dir, dist_dir, args):
    build_args = ['--out-dir={}'.format(out_dir)]
    build_args = ['--dist-dir={}'.format(dist_dir)]
    build_args.append('--host={}'.format(args.system))
    return build_args


def install_file(file_name, src_dir, dst_dir):
    src_file = os.path.join(src_dir, file_name)
    dst_file = os.path.join(dst_dir, file_name)

    print('Copying {} to {}...'.format(src_file, dst_file))
    if os.path.isdir(src_file):
        _install_dir(src_file, dst_file)
    elif os.path.islink(src_file):
        _install_symlink(src_file, dst_file)
    else:
        _install_file(src_file, dst_file)


def _install_dir(src_dir, dst_dir):
    parent_dir = os.path.normpath(os.path.join(dst_dir, '..'))
    if not os.path.exists(parent_dir):
        os.makedirs(parent_dir)
    shutil.copytree(src_dir, dst_dir, symlinks=True)


def _install_symlink(src_file, dst_file):
    dirname = os.path.dirname(dst_file)
    if not os.path.exists(dirname):
        os.makedirs(dirname)
    link_target = os.readlink(src_file)
    os.symlink(link_target, dst_file)


def _install_file(src_file, dst_file):
    dirname = os.path.dirname(dst_file)
    if not os.path.exists(dirname):
        os.makedirs(dirname)
    # copy2 is just copy followed by copystat (preserves file metadata).
    shutil.copy2(src_file, dst_file)


def build_clang(out_dir, dist_dir, args):
    print('Building Clang...')
    invoke_build('build-llvm.py', common_build_args(out_dir, dist_dir, args))


def build_gcc(out_dir, dist_dir, args):
    print('Building GCC...')
    build_args = common_build_args(out_dir, dist_dir, args)
    if args.arch is not None:
        build_args.append('--arch={}'.format(args.arch))
    invoke_build('build-gcc.py', build_args)


def build_shader_tools(out_dir, dist_dir, args):
    print('Building shader tools...')
    build_args = common_build_args(out_dir, dist_dir, args)
    invoke_build('build-shader-tools.py', build_args)


def build_host_tools(out_dir, dist_dir, args):
    build_args = common_build_args(out_dir, dist_dir, args)

    print('Building ndk-stack...')
    invoke_external_build(
        'ndk/sources/host-tools/ndk-stack/build.py', build_args)

    print('Building ndk-depends...')
    invoke_external_build(
        'ndk/sources/host-tools/ndk-depends/build.py', build_args)

    print('Building awk...')
    invoke_external_build(
        'ndk/sources/host-tools/nawk-20071023/build.py', build_args)

    print('Building make...')
    invoke_external_build(
        'ndk/sources/host-tools/make-3.81/build.py', build_args)

    if args.system in ('windows', 'windows64'):
        print('Building toolbox...')
        invoke_external_build(
            'ndk/sources/host-tools/toolbox/build.py', build_args)

    print('Building Python...')
    invoke_external_build('toolchain/python/build.py', build_args)

    print('Building GDB...')
    invoke_external_build('toolchain/gdb/build.py', build_args)

    print('Building YASM...')
    invoke_external_build('toolchain/yasm/build.py', build_args)

    package_host_tools(out_dir, dist_dir, args.system)


def package_host_tools(out_dir, dist_dir, host):
    packages = [
        'gdb-multiarch-7.11',
        'ndk-awk',
        'ndk-depends',
        'ndk-make',
        'ndk-python',
        'ndk-stack',
        'ndk-yasm',
    ]

    files = [
        'ndk-gdb',
        'ndk-gdb.py',
        'ndk-which',
    ]

    if host in ('windows', 'windows64'):
        packages.append('toolbox')
        files.append('ndk-gdb.cmd')

    host_tag = build_support.host_to_tag(host)

    package_names = [p + '-' + host_tag + '.tar.bz2' for p in packages]
    for package_name in package_names:
        package_path = os.path.join(out_dir, package_name)
        subprocess.check_call(['tar', 'xf', package_path, '-C', out_dir])

    for f in files:
        shutil.copy2(f, os.path.join(out_dir, 'host-tools/bin'))

    build_support.merge_license_files(
        os.path.join(out_dir, 'host-tools/NOTICE'), [
            build_support.android_path('toolchain/gdb/gdb-7.11/COPYING'),
            build_support.ndk_path('sources/host-tools/nawk-20071023/NOTICE'),
            build_support.ndk_path('sources/host-tools/ndk-depends/NOTICE'),
            build_support.ndk_path('sources/host-tools/make-3.81/COPYING'),
            build_support.android_path(
                'toolchain/python/Python-2.7.5/LICENSE'),
            build_support.ndk_path('sources/host-tools/ndk-stack/NOTICE'),
            build_support.ndk_path('sources/host-tools/toolbox/NOTICE'),
            build_support.android_path('toolchain/yasm/COPYING'),
            build_support.android_path('toolchain/yasm/BSD.txt'),
            build_support.android_path('toolchain/yasm/Artistic.txt'),
            build_support.android_path('toolchain/yasm/GNU_GPL-2.0'),
            build_support.android_path('toolchain/yasm/GNU_LGPL-2.0'),
        ])

    package_name = 'host-tools-' + host_tag
    path = os.path.join(out_dir, 'host-tools')
    build_support.make_package(package_name, path, dist_dir)


def build_gdbserver(out_dir, dist_dir, args):
    print('Building gdbserver...')
    build_args = common_build_args(out_dir, dist_dir, args)
    if args.arch is not None:
        build_args.append('--arch={}'.format(args.arch))
    invoke_build('build-gdbserver.py', build_args)


def _build_stl(out_dir, dist_dir, args, stl):
    build_args = common_build_args(out_dir, dist_dir, args)
    if args.arch is not None:
        build_args.append('--arch={}'.format(args.arch))
    script = 'ndk/sources/cxx-stl/{}/build.py'.format(stl)
    invoke_external_build(script, build_args)


def build_gnustl(out_dir, dist_dir, args):
    print('Building gnustl...')
    _build_stl(out_dir, dist_dir, args, 'gnu-libstdc++')


def build_libcxx(out_dir, dist_dir, args):
    print('Building libc++...')
    _build_stl(out_dir, dist_dir, args, 'llvm-libc++')


def build_stlport(out_dir, dist_dir, args):
    print('Building stlport...')
    _build_stl(out_dir, dist_dir, args, 'stlport')


def build_platforms(out_dir, dist_dir, args):
    print('Building platforms...')
    build_args = common_build_args(out_dir, dist_dir, args)
    invoke_build('build-platforms.py', build_args)


def build_libshaderc(_, dist_dir, __):
    print('Building libshaderc...')
    shaderc_root_dir = build_support.android_path('external/shaderc')

    copies = [
        {
            'source_dir': os.path.join(shaderc_root_dir, 'shaderc'),
            'dest_dir': 'shaderc',
            'files': [
                'Android.mk', 'libshaderc/Android.mk',
                'libshaderc_util/Android.mk',
                'third_party/Android.mk',
                'utils/update_build_version.py',
                'CHANGES',
            ],
            'dirs': [
                'libshaderc/include', 'libshaderc/src',
                'libshaderc_util/include', 'libshaderc_util/src',
            ],
        },
        {
            'source_dir': os.path.join(shaderc_root_dir, 'spirv-tools'),
            'dest_dir': 'shaderc/third_party/spirv-tools',
            'files': [
                'utils/generate_grammar_tables.py',
                'utils/update_build_version.py',
                'CHANGES',
            ],
            'dirs': ['include', 'source'],
        },
        {
            'source_dir': os.path.join(shaderc_root_dir, 'spirv-headers'),
            'dest_dir':
                'shaderc/third_party/spirv-tools/external/spirv-headers',
            'dirs': ['include'],
            'files': [
                'include/spirv/1.0/spirv.py',
                'include/spirv/1.1/spirv.py'
            ],
        },
        {
            'source_dir': os.path.join(shaderc_root_dir, 'glslang'),
            'dest_dir': 'shaderc/third_party/glslang',
            'files': ['glslang/OSDependent/osinclude.h'],
            'dirs': [
                'SPIRV',
                'OGLCompilersDLL',
                'glslang/GenericCodeGen',
                'hlsl',
                'glslang/Include',
                'glslang/MachineIndependent',
                'glslang/OSDependent/Unix',
                'glslang/Public',
            ],
        },
    ]

    default_ignore_patterns = shutil.ignore_patterns(
        "*CMakeLists.txt",
        "*.py",
        "*test.h",
        "*test.cc")

    temp_dir = tempfile.mkdtemp()
    shaderc_path = os.path.join(temp_dir, 'shaderc')
    try:
        for properties in copies:
            source_dir = properties['source_dir']
            dest_dir = os.path.join(temp_dir, properties['dest_dir'])
            for d in properties['dirs']:
                src = os.path.join(source_dir, d)
                dst = os.path.join(dest_dir, d)
                print(src, " -> ", dst)
                shutil.copytree(src, dst,
                                ignore=default_ignore_patterns)
            for f in properties['files']:
                print(source_dir, ':', dest_dir, ":", f)
                # Only copy if the source file exists.  That way
                # we can update this script in anticipation of
                # source files yet-to-come.
                if os.path.exists(os.path.join(source_dir, f)):
                    install_file(f, source_dir, dest_dir)
                else:
                    print(source_dir, ':', dest_dir, ":", f, "SKIPPED")

        shaderc_shaderc_dir = os.path.join(shaderc_root_dir, 'shaderc')
        build_support.merge_license_files(
            os.path.join(shaderc_path, 'NOTICE'), [
                os.path.join(shaderc_shaderc_dir, 'LICENSE'),
                os.path.join(shaderc_shaderc_dir,
                             'third_party',
                             'LICENSE.spirv-tools'),
                os.path.join(shaderc_shaderc_dir,
                             'third_party',
                             'LICENSE.glslang')])
        build_support.make_package('shaderc', shaderc_path, dist_dir)
    finally:
        shutil.rmtree(temp_dir)


def build_cpufeatures(_, dist_dir, __):
    path = build_support.ndk_path('sources/android/cpufeatures')
    build_support.make_package('cpufeatures', path, dist_dir)


def build_native_app_glue(_, dist_dir, __):
    path = build_support.ndk_path('sources/android/native_app_glue')
    build_support.make_package('native_app_glue', path, dist_dir)


def build_ndk_helper(_, dist_dir, __):
    path = build_support.ndk_path('sources/android/ndk_helper')
    build_support.make_package('ndk_helper', path, dist_dir)


def build_gtest(_, dist_dir, __):
    path = build_support.ndk_path('sources/third_party/googletest')
    build_support.make_package('gtest', path, dist_dir)


def build_sysroot(_out_dir, dist_dir, args):
    temp_dir = tempfile.mkdtemp()
    try:
        path = build_support.android_path('prebuilts/ndk/platform/sysroot')
        install_path = os.path.join(temp_dir, 'sysroot')
        shutil.copytree(path, install_path)
        if args.system != 'linux':
            # linux/netfilter has some headers with names that differ only by
            # case, which can't be extracted to a case-insensitive filesystem,
            # which are the defaults for Darwin and Windows :(
            #
            # There isn't really a good way to decide which of these to keep
            # and which to remove. The capitalized versions expose different
            # APIs, but we can't keep both. So far no one has filed bugs about
            # needing either API, so let's just dedup them consistently and we
            # can change that if we hear otherwise.
            remove_paths = [
                'usr/include/linux/netfilter_ipv4/ipt_ECN.h',
                'usr/include/linux/netfilter_ipv4/ipt_TTL.h',
                'usr/include/linux/netfilter_ipv6/ip6t_HL.h',
                'usr/include/linux/netfilter/xt_CONNMARK.h',
                'usr/include/linux/netfilter/xt_DSCP.h',
                'usr/include/linux/netfilter/xt_MARK.h',
                'usr/include/linux/netfilter/xt_RATEEST.h',
                'usr/include/linux/netfilter/xt_TCPMSS.h',
            ]
            for remove_path in remove_paths:
                os.remove(os.path.join(install_path, remove_path))

        build_support.make_package('sysroot', install_path, dist_dir)
    finally:
        shutil.rmtree(temp_dir)


def build_vulkan(out_dir, dist_dir, args):
    print('Constructing Vulkan validation layer source...')
    vulkan_root_dir = build_support.android_path(
        'external/vulkan-validation-layers')

    copies = [
        {
            'source_dir': vulkan_root_dir,
            'dest_dir': 'vulkan/src',
            'files': [
                'vk-generate.py',
                'vk_helper.py',
                'generator.py',
                'lvl_genvk.py',
                'threading_generator.py',
                'parameter_validation_generator.py',
                'unique_objects_generator.py',
                'reg.py',
                'source_line_info.py',
                'vulkan.py',
                'vk.xml'
            ],
            'dirs': [
                'layers', 'include', 'tests', 'common', 'libs'
            ],
        },
        {
            'source_dir': vulkan_root_dir + '/loader',
            'dest_dir': 'vulkan/src/loader',
            'files': [
                'vk_loader_platform.h',
                'vk_loader_layer.h'
            ],
            'dirs': [],
        }
    ]

    default_ignore_patterns = shutil.ignore_patterns(
        "*CMakeLists.txt",
        "*test.cc",
        "linux",
        "windows")

    vulkan_path = os.path.join(out_dir, 'vulkan/src')
    for properties in copies:
        source_dir = properties['source_dir']
        dest_dir = os.path.join(out_dir, properties['dest_dir'])
        for d in properties['dirs']:
            src = os.path.join(source_dir, d)
            dst = os.path.join(dest_dir, d)
            shutil.rmtree(dst, True)
            shutil.copytree(src, dst,
                            ignore=default_ignore_patterns)
        for f in properties['files']:
            install_file(f, source_dir, dest_dir)

    # Copy Android build components
    print('Copying Vulkan build components...')
    src = os.path.join(vulkan_root_dir, 'build-android')
    dst = os.path.join(vulkan_path, 'build-android')
    shutil.rmtree(dst, True)
    shutil.copytree(src, dst, ignore=default_ignore_patterns)
    print('Copying finished')

    # Copy binary validation layer libraries
    print('Copying Vulkan binary validation layers...')
    src = build_support.android_path('prebuilts/ndk/vulkan-validation-layers')
    dst = os.path.join(vulkan_path, 'build-android/jniLibs')
    shutil.rmtree(dst, True)
    shutil.copytree(src, dst, ignore=default_ignore_patterns)
    print('Copying finished')

    build_support.merge_license_files(
        os.path.join(vulkan_path, 'NOTICE'),
        [os.path.join(vulkan_root_dir, 'LICENSE.txt')])

    build_cmd = [
        'bash', vulkan_path + '/build-android/android-generate.sh'
    ]
    print('Generating generated layers...')
    subprocess.check_call(build_cmd)
    print('Generation finished')

    build_args = common_build_args(out_dir, dist_dir, args)
    if args.arch is not None:
        build_args.append('--arch={}'.format(args.arch))
    build_args.append('--no-symbols')

    # TODO: Verify source packaged properly
    print('Packaging Vulkan source...')
    src = os.path.join(out_dir, 'vulkan')
    build_support.make_package('vulkan', src, dist_dir)
    print('Packaging Vulkan source finished')


def build_ndk_build(_, dist_dir, __):
    path = build_support.ndk_path('build')
    build_support.make_package('ndk-build', path, dist_dir)


def build_python_packages(_, dist_dir, __):
    # Stage the files in a temporary directory to make things easier.
    temp_dir = tempfile.mkdtemp()
    try:
        path = os.path.join(temp_dir, 'python-packages')
        shutil.copytree(
            build_support.android_path('development/python-packages'), path)
        build_support.make_package('python-packages', path, dist_dir)
    finally:
        shutil.rmtree(temp_dir)


def build_gabixx(_out_dir, dist_dir, _args):
    print('Building gabi++...')
    path = build_support.ndk_path('sources/cxx-stl/gabi++')
    build_support.make_package('gabixx', path, dist_dir)


def build_system_stl(_out_dir, dist_dir, _args):
    print('Building system-stl...')
    path = build_support.ndk_path('sources/cxx-stl/system')
    build_support.make_package('system-stl', path, dist_dir)


def build_libandroid_support(_out_dir, dist_dir, _args):
    print('Building libandroid_support...')
    path = build_support.ndk_path('sources/android/support')
    build_support.make_package('libandroid_support', path, dist_dir)


def build_libcxxabi(_out_dir, dist_dir, _args):
    print('Building libc++abi...')
    path = build_support.android_path('external/libcxxabi')
    build_support.make_package('libcxxabi', path, dist_dir)


def build_simpleperf(out_dir, dist_dir, _args):
    print('Building simpleperf...')
    install_dir = os.path.join(out_dir, 'simpleperf')
    if os.path.exists(install_dir):
        shutil.rmtree(install_dir)
    os.makedirs(install_dir)

    simpleperf_path = build_support.android_path('prebuilts/simpleperf')
    shutil.copytree(os.path.join(simpleperf_path, 'android'),
                    os.path.join(install_dir, 'android'))

    shutil.copy2(
        os.path.join(simpleperf_path, 'simpleperf_report.py'), install_dir)
    shutil.copy2(os.path.join(simpleperf_path, 'README.md'), install_dir)
    shutil.copy2(os.path.join(simpleperf_path, 'NOTICE'), install_dir)

    build_support.make_package('simpleperf', install_dir, dist_dir)


def launch_build(build_name, build_func, out_dir, dist_dir, args, log_dir):
    log_path = os.path.join(log_dir, build_name) + '.log'
    tee = subprocess.Popen(["tee", log_path], stdin=subprocess.PIPE)
    try:
        os.dup2(tee.stdin.fileno(), sys.stdout.fileno())
        os.dup2(tee.stdin.fileno(), sys.stderr.fileno())

        try:
            build_func(out_dir, dist_dir, args)
            return build_name, True, log_path
        except Exception:  # pylint: disable=broad-except
            traceback.print_exc()
            return build_name, False, log_path
    finally:
        tee.terminate()
        tee.wait()


def main():
    total_timer = build_support.Timer()
    total_timer.start()

    # It seems the build servers run us in our own session, in which case we
    # get EPERM from `setpgrp`. No need to call this in that case because we
    # will already be the process group leader.
    if os.getpid() != os.getsid(os.getpid()):
        os.setpgrp()

    parser = ArgParser()
    args = parser.parse_args()

    if args.module is None:
        modules = ALL_MODULES
    else:
        modules = {args.module}

    if args.host_only:
        modules = {
            'clang',
            'gcc',
            'host-tools',
            'ndk-build',
            'python-packages',
            'shader_tools',
            'simpleperf',
        }

    required_package_modules = ALL_MODULES
    have_required_modules = required_package_modules <= modules
    if (args.package and have_required_modules) or args.force_package:
        do_package = True
    else:
        do_package = False

    # TODO(danalbert): wine?
    # We're building the Windows packages from Linux, so we can't actually run
    # any of the tests from here.
    if args.system.startswith('windows') or not do_package:
        args.test = False

    # Disable buffering on stdout so the build output doesn't hide all of our
    # "Building..." messages.
    sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', 0)

    os.chdir(os.path.dirname(os.path.realpath(__file__)))

    # Set ANDROID_BUILD_TOP.
    if 'ANDROID_BUILD_TOP' not in os.environ:
        os.environ['ANDROID_BUILD_TOP'] = os.path.realpath('..')

    out_dir = build_support.get_out_dir()
    dist_dir = build_support.get_dist_dir(out_dir)
    tmp_dir = os.path.join(out_dir, 'build')
    if os.path.exists(tmp_dir):
        shutil.rmtree(tmp_dir)
    os.mkdir(tmp_dir)

    os.environ['TMPDIR'] = tmp_dir

    print('Cleaning up...')
    invoke_build('dev-cleanup.sh')

    module_builds = collections.OrderedDict([
        ('clang', build_clang),
        ('cpufeatures', build_cpufeatures),
        ('gabi++', build_gabixx),
        ('gcc', build_gcc),
        ('gdbserver', build_gdbserver),
        ('gnustl', build_gnustl),
        ('gtest', build_gtest),
        ('host-tools', build_host_tools),
        ('libandroid_support', build_libandroid_support),
        ('libc++', build_libcxx),
        ('libc++abi', build_libcxxabi),
        ('libshaderc', build_libshaderc),
        ('native_app_glue', build_native_app_glue),
        ('ndk-build', build_ndk_build),
        ('ndk_helper', build_ndk_helper),
        ('platforms', build_platforms),
        ('python-packages', build_python_packages),
        ('shader_tools', build_shader_tools),
        ('simpleperf', build_simpleperf),
        ('stlport', build_stlport),
        ('sysroot', build_sysroot),
        ('system-stl', build_system_stl),
        ('vulkan', build_vulkan),
    ])

    print('Building modules: {}'.format(' '.join(modules)))
    print('Machine has {} CPUs'.format(multiprocessing.cpu_count()))

    log_dir = os.path.join(dist_dir, 'logs')
    if not os.path.exists(log_dir):
        os.makedirs(log_dir)

    build_timer = build_support.Timer()
    with build_timer:
        workqueue = ndk.workqueue.WorkQueue(args.jobs)
        try:
            for name, build_func in module_builds.iteritems():
                if name in modules:
                    workqueue.add_task(
                        launch_build, name, build_func, out_dir, dist_dir,
                        args, log_dir)

            while not workqueue.finished():
                build_name, result, log_path = workqueue.get_result()
                if result:
                    print('BUILD SUCCESSFUL: ' + build_name)
                else:
                    # Kill all the children so the error we print appears last.
                    workqueue.terminate()
                    workqueue.join()

                    print('BUILD FAILED: ' + build_name)
                    with open(log_path, 'r') as log_file:
                        contents = log_file.read()
                        print(contents)

                        # The build server has a build_error.log file that is
                        # supposed to be the short log of the failure that
                        # stopped the build. Append our failing log to that.
                        build_error_log = os.path.join(
                            dist_dir, 'logs/build_error.log')
                        with open(build_error_log, 'a') as error_log:
                            error_log.write('\n')
                            error_log.write(contents)
                    sys.exit(1)
        finally:
            workqueue.terminate()
            workqueue.join()

    package_timer = build_support.Timer()
    with package_timer:
        if do_package:
            package_ndk(out_dir, dist_dir, args)

    good = True
    test_timer = build_support.Timer()
    with test_timer:
        if args.test:
            good = test_ndk(out_dir, dist_dir, args)
            print()  # Blank line between test results and timing data.

    total_timer.finish()

    print('Finished {}'.format('successfully' if good else 'unsuccessfully'))
    print('Build: {}'.format(build_timer.duration))
    print('Packaging: {}'.format(package_timer.duration))
    print('Testing: {}'.format(test_timer.duration))
    print('Total: {}'.format(total_timer.duration))

    try:
        # notify-send sends a desktop notification on Ubuntu.
        subject = 'NDK Build {}!'.format('Passed' if good else 'Failed')
        body = 'Build finished in {}'.format(total_timer.duration)
        subprocess.call(['notify-send', subject, body])
    except OSError:
        pass

    sys.exit(not good)


if __name__ == '__main__':
    main()
