CXX ?= g++
BUILD_DIR ?= build
TARGET := $(BUILD_DIR)/ksearch

CXXFLAGS ?= -O3 -march=native -std=c++17 -pthread -Wall -Wextra -Wpedantic
CPPFLAGS ?=
LDFLAGS ?= -pthread
LDLIBS ?= -lgmpxx -lgmp

ifneq ($(wildcard /opt/homebrew/include/gmp.h),)
CPPFLAGS += -I/opt/homebrew/include
LDFLAGS += -L/opt/homebrew/lib
endif

ifneq ($(wildcard /usr/local/include/gmp.h),)
CPPFLAGS += -I/usr/local/include
LDFLAGS += -L/usr/local/lib
endif

.PHONY: all clean

all: $(TARGET)

$(TARGET): src/ksearch.cpp | $(BUILD_DIR)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $< -o $@ $(LDFLAGS) $(LDLIBS)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

clean:
	rm -rf $(BUILD_DIR)
