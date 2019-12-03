import Base: +, -, *, /, %, abs
import Base: &, |, !, Bool, ==, !=
import Base: <, <=, >, >=
import Base: exp, log, sqrt, ^
import Base: sin, cos, tan, asin, acos, atan
import ResumableFunctions: @yield, @resumable

@resumable function sin(z, x_::Out)
  x = asin(z)
  # TODO: this produces duplicates if x == pi/2
  while true
    @yield x
    @yield (pi - x)
    x += 2*pi
  end
end

@resumable function cos(z, x_::Out)
  x = acos(z)
  while true
    @yield x
    @yield (2*pi - x)
    x += 2*pi
  end
end

@resumable function tan(z, x_::Out)
  x = atan(z)
  while true
    @yield x
    x += pi
  end
end

@resumable function ^(z, x_::Out, y)
  @yield exp(log(z) / y)
end

@resumable function ^(z, x, y_::Out)
  @yield log(z) / log(x)
end

@resumable function sqrt(z, x_::Out)
  @yield (z*z)
end

@resumable function exp(z, x_::Out)
  @yield log(z)
end

@resumable function log(z, x_::Out)
  @yield exp(z)
end

@resumable function abs(z, x_::Out)
  @yield z
  @yield (-z)
end

@resumable function +(z, x_::Out)
  # +x == z ==> x = z
  @yield z
end

@resumable function +(z, x, y_::Out)
  # x + y == z  ==>  y = z - x
  @yield (z - x)
end

@resumable function +(z, x_::Out, y)
  # x + y == z  ==>  x = z - y
  @yield (z - y)
end

@resumable function +(z::T, x_::Out, y_::Out) where {T <: Integer}
  x = typemin(T)
  while true
    for y in +(z, x, Out())
      @yield (x, y)
    end
    if x == typemax(T)
      break
    end
    x += 1
  end
end

@resumable function -(z, x_::Out)
  # unary -
  @yield (-z)
end

@resumable function -(z, x, y_::Out)
  # x - y == z  ==>  y = x - z
  @yield (x - z)
end

@resumable function -(z, x_::Out, y)
  # x - y == z  ==>  x = z + y
  @yield (z + y)
end

@resumable function -(z::T, x_::Out, y_::Out) where {T <: Integer}
  x = typemin(T)
  while true
    for y in -(z, x, Out())
      @yield (x, y)
    end
    if x == typemax(T)
      break
    end
    x += 1
  end
end

# For multiplication, distinguish between integers and floats.
# For integers, we only produce a result if the result is an integer.
@resumable function *(z::T, x::T, y_::Out) where {T <: Integer}
  # x * y == z  ==>  y = z / x
  if mod(z, x) == 0
    @yield div(z, x)
  end
end

@resumable function *(z, x, y_::Out)
  # x * y == z  ==>  y = z / x
  @yield z / x
end

@resumable function *(z::T, x_::Out, y::T) where {T <: Integer}
  # x * y == z  ==>  x = z / y
  if mod(z, y) == 0
    @yield div(z, y)
  end
end

@resumable function *(z, x_::Out, y)
  # x * y == z  ==>  x = z / y
  @yield z / y
end

@resumable function *(z::T, x_::Out, y_::Out) where {T <: Integer}
  x = typemin(T)
  while true
    for y in *(z, x, Out())
      @yield (x, y)
    end
    if x == typemax(T)
      break
    end
    x += 1
  end
end

@resumable function *(z, x_::Out, y_::Out)
  error("* cannot be materialized")
end

@resumable function /(z, x, y_::Out)
  # x / y == z  ==> y = x / z
  @yield x / z
end

@resumable function /(z, x_::Out, y)
  # x / y == z  ==> x = y * z
  @yield y * z
end

@resumable function /(z, x_::Out, y_::Out)
  error("/ cannot be materialized")
end

@resumable function %(z::T, x::T, y_::Out) where {T <: Integer}
  # x % y == z ==> x == ay + z for all a
  a = typemin(T)
  while true
    if a != 0
      @yield div(x - z, a)
    end
    if a == typemax(T)
      break
    end
    a += 1
  end
end

@resumable function %(z::T, x_::Out, y::T) where {T <: Integer}
  # x % y == z ==> x == ay + z for all a
  a = typemin(T)
  while true
    @yield (a*y) + z
    if a == typemax(T)
      break
    end
    a += 1
  end
end

@resumable function %(z, x_::Out, y_::Out)
  error("% cannot be materialized")
end

@resumable function <(z::Bool, x_::Out, y::T) where {T <: Integer}
  for x in >(z, y, Out())
    @yield x
  end
end

@resumable function <=(z::Bool, x_::Out, y::T) where {T <: Integer}
  for x in >=(z, y, Out())
    @yield x
  end
end

@resumable function >(z::Bool, x_::Out, y::T) where {T <: Integer}
  for x in <(z, y, Out())
    @yield x
  end
end

@resumable function >=(z::Bool, x_::Out, y::T) where {T <: Integer}
  for x in <=(z, y, Out())
    @yield x
  end
end

@resumable function <(z::Bool, x::T, y_::Out) where {T <: Integer}
  if z
    y = x+1
    while x < y
      @yield y
      y += 1
    end
  else
    y = x
    while !(x < y)
      @yield y
      y -= 1
    end
  end
end

@resumable function <=(z::Bool, x::T, y_::Out) where {T <: Integer}
  if z
    y = x
    while x <= y
      @yield y
      y += 1
    end
  else
    y = x-1
    while !(x <= y)
      @yield y
      y -= 1
    end
  end
end

@resumable function >(z::Bool, x::T, y_::Out) where {T <: Integer}
  if z
    y = x-1
    while x > y
      @yield y
      y -= 1
    end
  else
    y = x
    while !(x > y)
      @yield y
      y += 1
    end
  end
end

@resumable function >=(z::Bool, x::T, y_::Out) where {T <: Integer}
  if z
    y = x
    while x >= y
      @yield y
      y -= 1
    end
  else
    y = x+1
    while !(x >= y)
      @yield y
      y += 1
    end
  end
end

@resumable function ==(z::Bool, x, y_::Out)
  if z
    @yield x
  else
    error("== cannot be materialized")
  end
end

@resumable function ==(z::Bool, x_::Out, y)
  if z
    @yield y
  else
    error("== cannot be materialized")
  end
end

@resumable function ==(z::Bool, x_::Out, y_::Out)
  error("== cannot be materialized")
end

@resumable function !=(z::Bool, x, y_::Out)
  if !z
    @yield x
  else
    error("!= cannot be materialized")
  end
end

@resumable function !=(z::Bool, x_::Out, y)
  if !z
    @yield y
  else
    error("!= cannot be materialized")
  end
end

@resumable function !=(z::Bool, x_::Out, y_::Out)
  error("!= cannot be materialized")
end

@resumable function Bool(z::Bool, x_::Out)
  @yield z
end

@resumable function !(z::Bool, x_::Out)
  @yield (!z)
end

@resumable function and(z::Bool, x::Bool, y_::Out)
  if z
    if x
      @yield true
    end
  else
    if x
      @yield false
    else
      @yield false
      @yield true
    end
  end
end

@resumable function and(z::Bool, x_::Out, y::Bool)
  for x in and(z, y, Out())
    @yield x
  end
end

@resumable function and(z::Bool, x_::Out, y_::Out)
  if z
    @yield (true, true)
  else
    @yield (false, false)
    @yield (false, true)
    @yield (true, false)
  end
end

@resumable function |(z::Bool, x::Bool, y_::Out)
  if z
    if x
      @yield false
      @yield true
    else
      @yield true
    end
  else
    if !x
      @yield false
    end
  end
end

@resumable function |(z::Bool, x_::Out, y::Bool)
  for x in |(z, y, Out())
    @yield x
  end
end

@resumable function |(z::Bool, x_::Out, y_::Out)
  if !z
    @yield (false, false)
  else
    @yield (false, true)
    @yield (true, false)
    @yield (true, true)
  end
end
