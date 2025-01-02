################################################################################
# Options
################################################################################
set (FLINT_DIR "" CACHE PATH "Path to the Flint lib and include directories")

################################################################################
# May be needed to install missing dependencies
################################################################################
include (ExternalProject)
include (IbexUtils)

################################################################################
# Looking for Flint, install it if not found
################################################################################
# Looking for flint/flint.h, result is written in FLINT_INCDIR
find_header_custom (FLINT "flint/flint.h" PATHS "${FLINT_DIR}")
# Looking for flint library, result is written in FLINT_LIB
find_library_custom (FLINT "flint" PATHS "${FLINT_DIR}")

if (FLINT_INCDIR AND FLINT_LIB)
  create_target_import_and_export (flint ${FLINT_LIB} FLINT_EXPORTFILE
                                          NAMESPACE Ibex::
                                          INCLUDE_DIRECTORIES ${FLINT_INCDIR})
else ()
  message (STATUS "Will install and use library Flint from 3rd/ subdirectory")
  #no patch
  #set (FLINT_PATCH "${CMAKE_CURRENT_SOURCE_DIR}/3rd/soplex-4.0.2.all.all.patch")

  #set (_shared "-DBUILD_SHARED_LIBS=Off")
  #if (BUILD_SHARED_LIBS)
  #  set (_shared "-DBUILD_SHARED_LIBS=On")
  #endif ()

  ExternalProject_Add (libflint_3rd
                        PREFIX flint-2.9.0
                        URL ${CMAKE_CURRENT_SOURCE_DIR}/3rd/flint-2.9.0.tar.gz
                        PATCH_COMMAND "" #patch -p1 -i ${SOPLEX_PATCH}
                        CMAKE_ARGS -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>
                        BUILD_IN_SOURCE 1
                        LOG_DOWNLOAD 1
                        LOG_CONFIGURE 1
                        LOG_INSTALL 1
                      )
  ExternalProject_Get_Property (libflint_3rd INSTALL_DIR)
  set (FLINT_LIBDIR "${INSTALL_DIR}/lib")
  set (FLINT_INCDIR "${INSTALL_DIR}/include")

  # absolute path to the library
  lib_get_abspath_from_name_type (FLINT_LIB ${FLINT_LIBDIR} flint YES)

  # this directory needs to exist during generation step to avoid CMake errors
  file (MAKE_DIRECTORY "${FLINT_INCDIR}")

  # install headers
  install (DIRECTORY ${FLINT_INCDIR}/ COMPONENT devtools
                                    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR_3RD})

  # 
  set (_incdir $<BUILD_INTERFACE:${FLINT_INCDIR}>$<INSTALL_INTERFACE:$<INSTALL_PREFIX>/${CMAKE_INSTALL_INCLUDEDIR_3RD}>)
  create_target_import_and_export (flint ${FLINT_LIB} FLINT_EXPORTFILE
                                        INSTALL NAMESPACE Ibex::
                                        INCLUDE_DIRECTORIES ${_incdir}
                                        COMPONENT devtools
                                        DEPENDS libflint_3rd)
  unset (INSTALL_DIR)
endif ()

list (APPEND EXPORTFILES "${FLINT_EXPORTFILE}")
set (EXPORTFILES "${EXPORTFILES}" PARENT_SCOPE)
list (APPEND IBEX_INCDIRS ${FLINT_INCDIR})
set (IBEX_INCDIRS ${IBEX_INCDIRS} PARENT_SCOPE)
