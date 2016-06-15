########################################################################
## CMAKE setting 
########################################################################
# Enforce some CMake policies
cmake_minimum_required(VERSION 3.0.1)

# Set project name
set (PROJECT_NAME ijit)
project (${PROJECT_NAME})

set(CMAKE_BUILD_TYPE Release)
 
set (PROJECT_SOURCE_DIR 
	${CMAKE_CURRENT_SOURCE_DIR}/src)

########################################################################
## dependencies 
########################################################################
#Set dependencies's dirs
set (PROJECT_INCLUDE_DIR
	${PROJECT_SOURCE_DIR} 
    ${PROJECT_SOURCE_DIR}/api
    ${PROJECT_SOURCE_DIR}/bpp
    ${PROJECT_SOURCE_DIR}/util)
       
include_directories("${PROJECT_INCLUDE_DIR}")

########################################################################
## target definition 
########################################################################
# Use instruction file(GLOB...) for wildcard additions
# this instruction search the directory tree when cmake is invoked and 
# put all files that match the pattern in the variables `SOURCES`
file(GLOB SOURCES 
          ${PROJECT_SOURCE_DIR}/api/*.cc 
          ${PROJECT_SOURCE_DIR}/bpp/*.cc 
          ${PROJECT_SOURCE_DIR}/util/*.cc)

# Set the compiler flags (specifically the c++11 one)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

# Generate the shared library from the SOURCES
add_library(${PROJECT_NAME} SHARED ${SOURCES})
 
########################################################################
## installation
# Set the location for library installation -- i.e., /usr/local/ijit/lib 
# Use "sudo make install" to apply if necessary.
########################################################################
set (PACKAGE_LIB_DESTINATION usr/local/ijit/lib)
set (PACKAGE_INC_DESTINATION usr/local/ijit/include)

install(TARGETS ${PROJECT_NAME} DESTINATION ${PACKAGE_LIB_DESTINATION})
