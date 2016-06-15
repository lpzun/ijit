# Enforce some CMake policies
cmake_minimum_required(VERSION 2.8.12)
# Set project name
project (ijit)

set(CMAKE_BUILD_TYPE Release)
 
set (PROJECT_SOURCE_DIR 
	${CMAKE_CURRENT_SOURCE_DIR}/src)
 
#Set 
set (PROJECT_INCLUDE_DIR
	${PROJECT_SOURCE_DIR} 
    ${PROJECT_SOURCE_DIR}/api
    ${PROJECT_SOURCE_DIR}/bpp
    ${PROJECT_SOURCE_DIR}/util)
       
include_directories("${PROJECT_INCLUDE_DIR}")
 
#However, the file(GLOB...) allows for wildcard additions:
file(GLOB SOURCES "src/*.cc")

# Set the compiler flags (specifically the c++11 one)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

#Generate the shared library from the sources
add_library(ijit SHARED ${SOURCES})
 
#Set the location for library installation -- i.e., /usr/lib in this case
# not really necessary in this example. Use "sudo make install" to apply
# install(TARGETS ijit DESTINATION /Users/lpzun/Peizun/IDETools/C++/workspace/ijit/lib)
