# Logic.jl

This library provides modal functions, logic programming, and pattern matching in Julia.

The basic idea is to solve for "unknowns"&mdash;unbound
variables&mdash;in _formulas_.
Solving the formula means to
find a binding for the variables.  There could be zero or more
solutions to the formula.

## Formulas

Patterns are actually the more basic construct.
Patterns are matched against values and produce bindings.
Actually, a formula is just a
`Bool` pattern. To solve a formula, one matches it against `true`.

Patterns:

- literals
- `x`  -- unknown x
- `_`
- `p where f` -- match p to v and match f with true
- `x(p...,)` -- calls and operators and 
- `k` -- constructors (how to distinguish from `x`?)
- `x(x=p...,)` -- match structs
- `p && q` -- can use `x && p` as an `@` pattern
- `p || q`
- (p...,) -- tuples (with ... splat operator!)
- [p...,] -- arrays (with ... splat operator!)
- [p...;] -- multi-dimensional arrays (with ... splat operator!)
- `p :: T` 
- `$x` -- evaluate, don't bind x
- `e`  -- evaluate e

## Solving formulas

The basic constructs are:

`@define` binds all unknowns in a formula. There should be exactly one
solution.

```julia
@define formula
  ...
end
```

`@define` binds all unknowns in a formula, returning an iterator.
There should be exactly one solution.


```julia
@foreach formula
  ...
end
```

## Patterns

Functions can be defined with _patterns_.
Patterns are matched against values and produce bindings, just like formulas.
Actually, a formula is just a
`Bool` pattern. To solve a formula, one matches it against `true`.

The formula `p = e` binds the value of expression `e` to the pattern
`e` and evaluates to `true` if there is a solution.

## Patterns in function definitions

**TODO**

```julia
@fun f(pat...)
  ...
end
```

## Modal functions (relations)

To extend the solver, one can add _modal_ functions.
This uses the `ResumableFunction` package.

For instance, the following function returns `x` such that `x+y = z`.

```julia
@resumable function +(z, x::Out, y)
  @yield z - y
end
```

Modal functions are defined for most of the builtin operators and functions.

## Materialized relations

**TODO**

One can also view collections as materialized relations.
This is implemented using modal functions.

## Credits

The design is based on the Ivo programming language developed by Nate
Nystrom and Igor Moreno Santos.  Unlike Ivo, the compilation strategy
follows the JMatch design [Liu and Myers, PADL 2003] using resumable
functions (aka iterators) rather than a LogicT-like monad [Kiselyov,
ICFP 2005]. Although we do use LogicT's `interleave` function to
ensure fairness between different iterators.  This turned out to be
simpler to implement using Julia macros (especially since there's
already a resumable function package).

The pattern matching implementation is based on Rematch.jl by RelationalAI Inc.
but uses modal functions rather than constructor patterns.

