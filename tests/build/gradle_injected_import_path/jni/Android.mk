LOCAL_PATH := $(call my-dir)

include $(CLEAR_VARS)
LOCAL_MODULE := foo
LOCAL_SRC_FILES := foo.cpp
LOCAL_SHARED_LIBRARIES := bar
include $(BUILD_SHARED_LIBRARY)

$(call import-module,injected/module)