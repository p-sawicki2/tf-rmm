
# Add test functionality
rmm_build_unittest(NAME granule
                   TARGET rmm-lib-realm
                   SOURCES "tests/granule.cpp"
                           "tests/test_harness.c"
                   ITERATIONS 1000)
