cmake_minimum_required(VERSION 3.5)
project(Transys)
set(CMAKE_CXX_STANDARD 11)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})
add_library(Transys STATIC transys.c)

add_custom_target(
    libtransys
    COMMAND cargo build --release
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/..
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/../src/*.rs
)
add_dependencies(Transys libtransys)

target_link_libraries(Transys ${CMAKE_CURRENT_SOURCE_DIR}/../target/release/libtransys.a)
target_include_directories(Transys PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
