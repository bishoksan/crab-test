# Ikos-core #

This project contains the core of Ikos, a static analyzer based on
abstract interpretation developed at NASA Ames Research Center. This
core consists of an implementation of a fixpoint algorithm and several
abstract numerical domains.

The directory include contains a CFG that interfaces with IKOS as well
as wrappers to execute backward and forward analyses on it.

# License #

This software is released under the terms and conditions of the NASA
Open Source Agreement (NOSA) Version 1.3 or later.

# Prerequisites #

The C++ compiler must support c++11
Boost and gmp  (if Boost and gmp are installed CMake is usually good at find them).

# Installation #
`
mkdir build && cd build  && cmake ../
`

# Usage #

The tests directory contains some examples of how to build CFGs and
how to compute invariants using different abstract domains.

`
build/tests/prog-1
`

# Some notes for implementing new numerical abstract domains #

The main task is to implement the following methods required by the
fixpoint algorithm:
  
    static AbsDomain top();
    
    static AbsDomain bottom();
    
    bool is_bottom ();

    bool is_top ();

    // Less or equal
    bool operator<=(AbsDomain o);

    // Join
    AbsDomain operator|(AbsDomain o);

    // Meet
    AbsDomain operator&(AbsDomain o);

    // Widening
    AbsDomain operator||(AbsDomain o);

    // Narrowing 
    AbsDomain operator&&(AbsDomain o);
    
In addition, it is also required to implement the api described in
numerical_domains_api.hpp:

    typedef linear_expression< Number, VariableName > linear_expression_t;
    typedef linear_constraint< Number, VariableName > linear_constraint_t;
    typedef linear_constraint_system< Number, VariableName > linear_constraint_system_t;
  
    // x = y op z
    virtual void apply(operation_t op, VariableName x, VariableName y, VariableName z) = 0; 

    // x = y op k
    virtual void apply(operation_t op, VariableName x, VariableName y, Number k) = 0; 

    // x = e
    virtual void assign(VariableName x, linear_expression_t e) = 0; 

    // assume (c);
    virtual void operator+=(linear_constraint_system_t csts) = 0;

    // Forget
    virtual void operator-=(VariableName v) = 0;

    virtual ~numerical_domain() { }
      
This api assumes the manipulation of linear expressions and linear
constraints both defined in linear_constraints.hpp so it is good to be
familiar with.

For non-relational domains it is highly recommend to build on the top
of separate_domains which provides an efficient implementation of a
fast mergeable integer map based on patricia trees. This map can be
used to map variable names to abstract values. The implementation of
intervals and congruences use it.