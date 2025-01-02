################################################################################
# Options
################################################################################
set (ARB_DIR "" CACHE PATH "Path to the Arb lib and include directories")

################################################################################
# May be needed to install missing dependencies
################################################################################
include (ExternalProject)
include (IbexUtils)

################################################################################
# Looking for Arb, install it if not found
################################################################################
# Looking for arb.h, result is written in ARB_INCDIR
find_header_custom (ARB "arb.h" PATHS "${ARB_DIR}")
# Looking for arb library, result is written in ARB_LIB
find_library_custom (ARB "arb" PATHS "${ARB_DIR}")

if (ARB_INCDIR AND ARB_LIB)
  create_target_import_and_export (arb ${ARB_LIB} ARB_EXPORTFILE
                                          NAMESPACE Ibex::
                                          INCLUDE_DIRECTORIES ${ARB_INCDIR})
else ()
  message (STATUS "Will install and use library Arb from 3rd/ subdirectory")
  #set (ARB_PATCH "${CMAKE_CURRENT_SOURCE_DIR}/3rd/arb-2.23.0.all.all.patch")

  #set (_shared "-DBUILD_SHARED_LIBS=Off")
  #if (BUILD_SHARED_LIBS)
  #  set (_shared "-DBUILD_SHARED_LIBS=On")
  #endif ()

  list(APPEND CMAKE_PREFIX_PATH "${CMAKE_BINARY_DIR}/flint/flint-2.9.0/")
  set (_libloc "-DCMAKE_PREFIX_PATH=${CMAKE_PREFIX_PATH}")

  ExternalProject_Add (libarb_3rd
                        PREFIX arb-2.23.0
                        URL ${CMAKE_CURRENT_SOURCE_DIR}/3rd/arb-2.23.0.tar.gz
                        #PATCH_COMMAND patch -p1 -i ${ARB_PATCH}
                        CMAKE_ARGS -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR> ${_libloc}
                        BUILD_IN_SOURCE 1
                        LOG_DOWNLOAD 1
                        LOG_CONFIGURE 1
                        LOG_INSTALL 1
                        DEPENDS Ibex::flint
                      )
  ExternalProject_Get_Property (libarb_3rd INSTALL_DIR)
  set (ARB_LIBDIR "${INSTALL_DIR}/lib")
  set (ARB_INCDIR "${INSTALL_DIR}/include")

  # absolute path to the library
  lib_get_abspath_from_name_type (ARB_LIB ${ARB_LIBDIR} arb YES)

  # this directory needs to exist during generation step to avoid CMake errors
  file (MAKE_DIRECTORY "${ARB_INCDIR}")

  # install headers
  install (DIRECTORY ${ARB_INCDIR}/ COMPONENT devtools
                                    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR_3RD})

  # 
  set (_incdir $<BUILD_INTERFACE:${ARB_INCDIR}>$<INSTALL_INTERFACE:$<INSTALL_PREFIX>/${CMAKE_INSTALL_INCLUDEDIR_3RD}>)
  create_target_import_and_export (arb ${ARB_LIB} ARB_EXPORTFILE
                                        INSTALL NAMESPACE Ibex::
                                        INCLUDE_DIRECTORIES ${_incdir}
                                        COMPONENT devtools
                                        DEPENDS libarb_3rd)
  unset (INSTALL_DIR)
endif ()

list (APPEND EXPORTFILES "${ARB_EXPORTFILE}")
set (EXPORTFILES "${EXPORTFILES}" PARENT_SCOPE)
list (APPEND IBEX_INCDIRS ${ARB_INCDIR})
set (IBEX_INCDIRS ${IBEX_INCDIRS} PARENT_SCOPE)
