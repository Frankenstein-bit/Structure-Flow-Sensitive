# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/f/SVFtype/SVF-SVF-2.5

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/f/SVFtype/SVF-SVF-2.5/build

# Utility rule file for install-Svf-stripped.

# Include any custom commands dependencies for this target.
include lib/CMakeFiles/install-Svf-stripped.dir/compiler_depend.make

# Include the progress variables for this target.
include lib/CMakeFiles/install-Svf-stripped.dir/progress.make

lib/CMakeFiles/install-Svf-stripped:
	cd /home/f/SVFtype/SVF-SVF-2.5/build/lib && /usr/bin/cmake -DCMAKE_INSTALL_COMPONENT="Svf" -DCMAKE_INSTALL_DO_STRIP=1 -P /home/f/SVFtype/SVF-SVF-2.5/build/cmake_install.cmake

install-Svf-stripped: lib/CMakeFiles/install-Svf-stripped
install-Svf-stripped: lib/CMakeFiles/install-Svf-stripped.dir/build.make
.PHONY : install-Svf-stripped

# Rule to build all files generated by this target.
lib/CMakeFiles/install-Svf-stripped.dir/build: install-Svf-stripped
.PHONY : lib/CMakeFiles/install-Svf-stripped.dir/build

lib/CMakeFiles/install-Svf-stripped.dir/clean:
	cd /home/f/SVFtype/SVF-SVF-2.5/build/lib && $(CMAKE_COMMAND) -P CMakeFiles/install-Svf-stripped.dir/cmake_clean.cmake
.PHONY : lib/CMakeFiles/install-Svf-stripped.dir/clean

lib/CMakeFiles/install-Svf-stripped.dir/depend:
	cd /home/f/SVFtype/SVF-SVF-2.5/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/f/SVFtype/SVF-SVF-2.5 /home/f/SVFtype/SVF-SVF-2.5/lib /home/f/SVFtype/SVF-SVF-2.5/build /home/f/SVFtype/SVF-SVF-2.5/build/lib /home/f/SVFtype/SVF-SVF-2.5/build/lib/CMakeFiles/install-Svf-stripped.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : lib/CMakeFiles/install-Svf-stripped.dir/depend
