"""
This library provides modal functions and pattern matching in Julia.

The design is based on the Ivo programming language.
Unlike Ivo, the compilation strategy follows the JMatch design
using resumable functions (aka iterators) rather than a LogicT-like monad.
This turned out to be simpler to implement using Julia macros
(especially since there's already a resumable function package).

The pattern matching implementation is based on Rematch.jl.
"""
module Logic

import MacroTools
import MacroTools: @capture

# Error when a formula has no solutions.
struct MatchFailure
  value
end

# Error when a formula has more than one solution.
struct MatchAmbiguous
  value
end

# How to translate a function definition with patterns?
#
#

# How to translate a relation definition?
#
# @rel +(in x, out y, in z)
#   y = z - x
#   @yield
# end
#
# -->
#
# @resumable
# function +(x, y::Out, z)
#   y = z - x
#   @yield y
# end
#
# Another example:
#
# @rel +(out x, out y, in z::T)
#   x = typemin(T)
#
#   while true
#     y = z - x
#     @yield
#
#     if x == typemax(T)
#       return
#     end
#     
#     x += 1
#   end
# end
#
# @let 1+x = 2
# ->
# x = +(1, Out, 2)

abstract type Mode end
struct In <: Mode end
struct Out <: Mode end

include("prims.jl")

# Returns true if the pattern has unknowns.
# If not, it can just be evaluated in forward mode.
function has_unknowns(pat, bound)::Bool
  # println("pat $pat")
  # println("bound $bound")

  if @capture(pat, p_ = e_)
    has_unknowns(p, bound)
  elseif @capture(pat, p_ in e_)
    has_unknowns(p, bound)
  elseif pat == :(_)
    true
  elseif !(pat isa Expr || pat isa Symbol)
    # constants (including strings, true and false)
    false
  elseif pat == :nothing || pat == :missing
    # nothing
    false
  elseif @capture(pat, _quote_macrocall) 
    false
  elseif @capture(pat, Symbol(_))
    false
  elseif @capture(pat, x_Symbol)
    ! (x in bound)
  elseif @capture(pat, p1_ || p2_)
    has_unknowns(p1, bound) || has_unknowns(p2, bound)
  elseif @capture(pat, p1_ && p2_)
    has_unknowns(p1, bound) || has_unknowns(p2, bound)
  elseif @capture(pat, (p1_ where p2_))
    has_unknowns(p1, bound) || has_unknowns(p2, bound)
  elseif @capture(pat, T_Symbol(ps__))
    # call (on a symbol)
    # there are some special cases
    # if T is + or *, 1+2+3+4+5 has the tree +(1,2,3,4,5)
    # 5x is *(5,:x)
    # T might be a struct name. Then the pattern is Foo(x=2, y=3)
    Base.any(p -> has_unknowns(p, bound), ps)
  elseif @capture(pat, (ps__,))
    # tuple
    Base.any(p -> has_unknowns(p, bound), ps)
  elseif @capture(pat, [ps__,])
    # array
    Base.any(p -> has_unknowns(p, bound), ps)
  elseif @capture(pat, [ps__;])
    # array
    Base.any(p -> has_unknowns(p, bound), ps)
  elseif @capture(pat, p_::T_)
    # type assert
    has_unknowns(p, bound)
  else
    # anything else must be evaluated in forward mode
    # T{a}
    # a[1,2,3]
    # if, while, for, etc
    # ? :
    # call on a lambda
    # lambda
    false
  end
end

function match_tuple(ps, v, i, body, bound, rename)
  println("ps $ps")
  if i > length(ps)
    body
  else
    @assert 1 <= i && i <= length(ps)
    # FIXME binds variables in the wrong order
    rest = match_tuple(ps, v, i+1, body, bound, rename)
    translate_match(ps[i], :($v[$i]), rest, bound, rename)
  end
end

# Some of this code is based on Rematch.jl.
# But rather than return a boolean, we eval the body for each
# solution.
function translate_match(pat, value, body, bound::Set{Symbol}, rename::Dict{Symbol,Symbol})
  if !has_unknowns(pat, bound)
    # constants and other forward-mode expressions
    quote
      if $pat == $value
        $body
      end
    end
  elseif @capture(pat, p_ = e_)
    # the pattern is a bind formula. the value should be true
    # note, unlike in a true relational language, we only bind
    # unknowns on the left; the term on the right is not a pattern
    body1 = translate_match(p, e, body, bound, rename)

    if value == true
      body1
    elseif value == false
      :(throw(MatchFailure(value)))
    else
      quote
        if $value
          $body1
        end
      end
    end
  elseif @capture(pat, p_ in e_)
    # the pattern is an `in` pattern (`<-` in Ivo).
    tmp = gensym()
    quote
      if $value
        for $tmp in $e
          $(translate_match(p, tmp, body, bound, rename))
        end
      else
        nothing
      end
    end
  elseif pat == :(_)
    tmp = gensym()
    quote
      let $tmp = $value;
        $body
      end
    end
  elseif @capture(pat, x_Symbol)
    # variable

    # if the pattern doesn't match, we don't want to set the variable,
    # so use a temporary

    # FIXME: don't rename yet
    tmp = x # get!(rename, x, gensym(x))

    if x in bound
      # already bound; eval in forward mode
      quote
        if $tmp == $value
          $body
        end
      end
    else
      println("$pat :: bound $bound + $x")
      push!(bound, x)
      quote
        let $tmp = $value;
          $body
        end
      end
    end
  elseif @capture(pat, p1_ || p2_)
    matched = gensym()
    v = gensym()

    bound1 = copy(bound)
    bound2 = copy(bound)

    body1 = translate_match(p1, v, :($matched = true), bound1, rename)
    body2 = translate_match(p2, v, :($matched = true), bound2, rename)

    union!(bound, intersect(bound1, bound2))

    quote
      let $v = $value;
        let $matched = false;
          begin
            $body1;
            if !$matched
              $body2
            end
            if $matched
              $body
            end
          end
        end
      end
    end
  elseif @capture(pat, p1_ && p2_)
    v = gensym()

    # HACK: compute the bound from p1 and use that for p2, but then redo with the original bound
    # have to do this because we pass the body in and bind in p2 first
    bound1 = copy(bound)
    translate_match(p1, v, :(), bound1, rename)

    body1 = translate_match(p1, v, translate_match(p2, v, body, bound1, rename), bound, rename)
    union!(bound, bound1)

    quote
      let $v = $value;
        $body1
      end
    end
  elseif @capture(pat, (p_ where guard_))
    # both p and guard can bind variables
    #
    # similar to &&, but matches the guard against true

    v = gensym()

    # HACK: compute the bound from p1 and use that for p2, but then redo with the original bound
    # have to do this because we pass the body in and bind in p2 first
    bound1 = copy(bound)
    translate_match(p, v, :(), bound1, rename)

    body1 = translate_match(p, v, translate_match(guard, true, body, bound1, rename), bound, rename)
    union!(bound, bound1)

    quote
      let $v = $value;
        $body1
      end
    end
  elseif @capture(pat, f_(ps__))
    result = gensym()

    begin
      # FIXME bound is wrong because of unknowns bound in earlier patterns are *not* unknowns in later patterns
      outputs = filter(p -> has_unknowns(p, bound), ps)

      inputs = map(p -> has_unknowns(p, bound) ? :(Out()) : p, ps)
      newcall = Expr(:call, f, value, inputs...)

      # println("pat ", pat)
      # println("value ", value)
      # println("f ", f)
      # println("ps ", ps)
      # println("inputs ", inputs)
      # println("outputs ", outputs)
      # println("newcall ", newcall)
      # println("newcall.head ", newcall.head)
      # println("newcall.args ", newcall.args)
      # for (i,a) in enumerate(newcall.args)
      #   println("newcall.args[$i] $a")
      # end

      if length(outputs) == 1
        quote
          for $result in $newcall
            $(translate_match(outputs[1], result, body, bound, rename))
          end
        end
      else
        results_pat = Expr(:tuple, outputs...)
        quote
          for $result in $newcall
            $(translate_match(results_pat, result, body, bound, rename))
          end
        end
      end
    end

    #=
    # struct or call
    # TODO TODO TODO
    #
    # eval the function, inject into monad if not overloaded
    # eval the input arguments
    # eval $value
    # select-thunk(apply-amb (f >>= mode-select [invert-mode ps]))

    (apply-amb u x) = u >>= \g -> g x   [g fresh]
    (apply-amb u x1 x2..xn) = (apply-amb (apply-amb u x1)
                                         x2..xn)

    select-thunk (amb ...)
        -- filter: if exactly one unique, done
                   if all normal, done
                   if all default, done
                   if normal and unique, error
                   if default and unique, throw out the default
                   if default and normal, throw out the default


        -- if there's one, choose it
        -- if there's more than one, MatchAmbiguous
        -- if there's zero, MatchFailure
        -- 

    
        =#
  elseif @capture(pat, (ps__,))
    # tuple
    v = gensym()

    quote
      let $v = $value
        if isa($v, Tuple)
          if length($v) == $(length(ps))
            $(match_tuple(ps, v, 1, body, bound, rename))
          end
        end
      end
    end
  elseif @capture(pat, [ps__,])
    # array
    v = gensym()
    w = gensym()
    quote
      let $v = $value
        if isa($v, AbstractArray)
          if length($v) == $(length(ps))
            $(match_tuple(ps, v, 1, body, bound, rename))
          end
        end
      end
    end
  elseif @capture(pat, p_::T_)
    # type assert
    v = gensym()
    quote
      let $v = $value
        if isa($v, $(esc(T)))
          $(translate_match(p, v, body, bound, rename))
        end
      end
    end
  else
    error("Unrecognized pattern syntax: $pat")
  end
end


"""
    @fun name(patterns...)
        ...
    end

    @fun name(patterns...) where guard
        ...
    end

Declare a function with pattern parameters.
"""
macro fun(name, argsbody)
    if @capture(argsbody, args_ = body_) &&
       @capture(args, (pats__)) &&
       @capture(body, begin body_ end)
        xs = map(p -> gensym(), pats)
        bound = Set{Symbol}()
        rename = Dict{Symbol,Symbol}()
        quote
            function $(esc(name))(xs...)
                $(translate_match(:($pats...,), Tuple(xs...), body, bound, rename))
            end
        end
    else
        error("Unrecognized fun syntax: $name $body")
    end
end

"""
    @rel name(patterns...)
        ...
    end

    @rel name(patterns...) where guard
        ...
    end

Declare a modal function (relation).
"""
macro rel(name, args, body)
    quote
        function $(esc(name))($args)
            $body
        end
    end
end

"""
    @foreach(formula)
        ...
    end

Iterate over all solutions of the formula. Unknowns in the formula are bound in the body.
"""
macro foreach(formula, body)
  println(formula)
  println(body)
  bound = Set{Symbol}()
  rename = Dict{Symbol,Symbol}()
  x = translate_match(formula, :true, body, bound, rename)
  println(x)
  x
end

"""
    @once(formula)
        ...
    end

Iterate over all solutions of the formula. Unknowns in the formula are bound in the body.
"""
macro once(formula, body)
  println(formula)
  println(body)
  bound = Set{Symbol}()
  rename = Dict{Symbol,Symbol}()
  x = translate_match(formula, :true, :(begin; $body; break; end), bound, rename)
  println(x)
  quote
    for _ in [()] 
      $x
    end
  end
end

"""
    @define(formula)

    @let formula begin
        body
    end

If `formula` has a solution, bind variables and return `true`.
Throws an error if there is not exactly one solution.
If there are no solutions, throw `MatchFailure`.
If there is more than one solutions, throw `MatchAmbiguous`.
"""
macro define(formula)
  #=
    quote
        begin
            apply_thunk(unwrap($translate_match(formula, :true, body)))
        end
    end
    =#
end

"""
    @match value begin
        pattern1 => result1
        pattern2 => result2
        ...
    end

Return `result` for the first matching `pattern`.
If there are no matches, throw `MatchFailure`.
If there are multiple matches, throw `MatchAmbiguous`.
"""
macro match(value, cases)
    # f = make_function(cases)
    quote
      # f($value)
    end
end

export MatchFailure, MatchAmbiguous
export @match
export @foreach, @once

end #module
