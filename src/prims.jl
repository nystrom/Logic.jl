import Base: +, -, *, /, abs

@resumable function abs(z, x_::Out)
  @yield z
  @yield (-z)
end

# override primitive operations with relational versions
@resumable function +(z, x_::Out)
  # +x == z ==> x = z
  @yield z
end

# override primitive operations with relational versions
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
    x = x+1
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
    x = x+1
  end
end

@resumable function *(z::T, x::T, y_::Out) where {T <: Integer}
  # x * y == z  ==>  y = z / x
  if mod(z, x) == 0
    @yield div(z, x)
  end
end

@resumable function *(z::T, x_::Out, y::T) where {T <: Integer}
  # x * y == z  ==>  x = z / y
  if mod(z, y) == 0
    @yield div(z, y)
  end
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
    x = x+1
  end
end
