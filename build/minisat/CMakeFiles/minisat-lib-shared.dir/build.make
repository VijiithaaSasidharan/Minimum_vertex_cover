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
CMAKE_COMMAND = /opt/homebrew/Cellar/cmake/3.22.2/bin/cmake

# The command to remove a file.
RM = /opt/homebrew/Cellar/cmake/3.22.2/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build

# Include any dependencies generated for this target.
include minisat/CMakeFiles/minisat-lib-shared.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include minisat/CMakeFiles/minisat-lib-shared.dir/compiler_depend.make

# Include the progress variables for this target.
include minisat/CMakeFiles/minisat-lib-shared.dir/progress.make

# Include the compile flags for this target's objects.
include minisat/CMakeFiles/minisat-lib-shared.dir/flags.make

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o: minisat/CMakeFiles/minisat-lib-shared.dir/flags.make
minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o: ../minisat/minisat/utils/Options.cc
minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o: minisat/CMakeFiles/minisat-lib-shared.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o -MF CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o.d -o CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o -c /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/utils/Options.cc

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.i"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/utils/Options.cc > CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.i

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.s"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/utils/Options.cc -o CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.s

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o: minisat/CMakeFiles/minisat-lib-shared.dir/flags.make
minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o: ../minisat/minisat/utils/System.cc
minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o: minisat/CMakeFiles/minisat-lib-shared.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o -MF CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o.d -o CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o -c /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/utils/System.cc

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.i"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/utils/System.cc > CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.i

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.s"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/utils/System.cc -o CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.s

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o: minisat/CMakeFiles/minisat-lib-shared.dir/flags.make
minisat/CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o: ../minisat/minisat/core/Solver.cc
minisat/CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o: minisat/CMakeFiles/minisat-lib-shared.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object minisat/CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT minisat/CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o -MF CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o.d -o CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o -c /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/core/Solver.cc

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.i"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/core/Solver.cc > CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.i

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.s"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/core/Solver.cc -o CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.s

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o: minisat/CMakeFiles/minisat-lib-shared.dir/flags.make
minisat/CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o: ../minisat/minisat/simp/SimpSolver.cc
minisat/CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o: minisat/CMakeFiles/minisat-lib-shared.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building CXX object minisat/CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT minisat/CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o -MF CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o.d -o CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o -c /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/simp/SimpSolver.cc

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.i"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/simp/SimpSolver.cc > CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.i

minisat/CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.s"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && /usr/bin/clang++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat/minisat/simp/SimpSolver.cc -o CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.s

# Object files for target minisat-lib-shared
minisat__lib__shared_OBJECTS = \
"CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o" \
"CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o" \
"CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o" \
"CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o"

# External object files for target minisat-lib-shared
minisat__lib__shared_EXTERNAL_OBJECTS =

minisat/libminisat.2.1.0.dylib: minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/Options.cc.o
minisat/libminisat.2.1.0.dylib: minisat/CMakeFiles/minisat-lib-shared.dir/minisat/utils/System.cc.o
minisat/libminisat.2.1.0.dylib: minisat/CMakeFiles/minisat-lib-shared.dir/minisat/core/Solver.cc.o
minisat/libminisat.2.1.0.dylib: minisat/CMakeFiles/minisat-lib-shared.dir/minisat/simp/SimpSolver.cc.o
minisat/libminisat.2.1.0.dylib: minisat/CMakeFiles/minisat-lib-shared.dir/build.make
minisat/libminisat.2.1.0.dylib: /Library/Developer/CommandLineTools/SDKs/MacOSX12.1.sdk/usr/lib/libz.tbd
minisat/libminisat.2.1.0.dylib: minisat/CMakeFiles/minisat-lib-shared.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Linking CXX shared library libminisat.dylib"
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/minisat-lib-shared.dir/link.txt --verbose=$(VERBOSE)
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && $(CMAKE_COMMAND) -E cmake_symlink_library libminisat.2.1.0.dylib libminisat.2.dylib libminisat.dylib

minisat/libminisat.2.dylib: minisat/libminisat.2.1.0.dylib
	@$(CMAKE_COMMAND) -E touch_nocreate minisat/libminisat.2.dylib

minisat/libminisat.dylib: minisat/libminisat.2.1.0.dylib
	@$(CMAKE_COMMAND) -E touch_nocreate minisat/libminisat.dylib

# Rule to build all files generated by this target.
minisat/CMakeFiles/minisat-lib-shared.dir/build: minisat/libminisat.dylib
.PHONY : minisat/CMakeFiles/minisat-lib-shared.dir/build

minisat/CMakeFiles/minisat-lib-shared.dir/clean:
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat && $(CMAKE_COMMAND) -P CMakeFiles/minisat-lib-shared.dir/cmake_clean.cmake
.PHONY : minisat/CMakeFiles/minisat-lib-shared.dir/clean

minisat/CMakeFiles/minisat-lib-shared.dir/depend:
	cd /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/minisat /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat /Users/vijii/Documents/ECE650/vsasidha-bmkmuthu/project/build/minisat/CMakeFiles/minisat-lib-shared.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : minisat/CMakeFiles/minisat-lib-shared.dir/depend

