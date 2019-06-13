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
"""Builds make for the NDK."""
from __future__ import print_function

import os
import site

site.addsitedir(os.path.join(os.path.dirname(__file__), '../../../build/lib'))
site.addsitedir(os.path.join(os.path.dirname(__file__), '../../..'))

# pylint: disable=import-error,wrong-import-position
import build_support
from ndk.hosts import Host
# pylint: enable=import-error,wrong-import-position


def main(args):
    build_cmd = [
        'bash', 'build-make.sh', '--try-64',
    ]

    if args.host.is_windows:
        build_cmd.append('--mingw')

    build_cmd.append('--build-dir=' + os.path.join(args.out_dir, 'make'))

    build_support.build(build_cmd, args, intermediate_package=True)

if __name__ == '__main__':
    build_support.run(main)
