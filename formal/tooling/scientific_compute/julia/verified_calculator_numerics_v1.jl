#!/usr/bin/env julia

# Independent numerical controls for the Verified Physics Calculator v1.
# Candidate-supplied callbacks are never executed: ODE/RGE and ensemble
# functions are interpreted from a closed declarative expression tree.

using JSON3
using OrdinaryDiffEq
using Printf
using SHA

fail(code, detail="") = error(isempty(detail) ? code : string(code, ":", detail))
ensure(test, code, detail="") = test ? nothing : fail(code, detail)

function canonical_json(value)
    if value === nothing
        return "null"
    elseif value isa Bool
        return value ? "true" : "false"
    elseif value isa Integer
        return string(value)
    elseif value isa AbstractFloat
        fail("BINARY_FLOAT_NOT_CANONICAL")
    elseif value isa String
        return String(JSON3.write(value))
    elseif value isa Vector
        return "[" * join(canonical_json.(value), ",") * "]"
    elseif value isa Dict
        names = sort(String.(collect(keys(value))))
        return "{" * join([String(JSON3.write(name)) * ":" * canonical_json(value[name]) for name in names], ",") * "}"
    end
    fail("CANONICAL_JSON_TYPE", string(typeof(value)))
end

function domain_digest(value, domain)
    bytes2hex(sha256(Vector{UInt8}(codeunits(domain * "\0" * canonical_json(value)))))
end

function expression_value(node, variables, time, state)
    op = node["op"]
    if op == "CONST"; return parse(Float64, node["value"]); end
    if op == "VAR"; return variables[node["name"]]; end
    if op == "TIME"; return time; end
    if op == "STATE"; return state[node["index"] + 1]; end
    if op == "NEG"; return -expression_value(node["argument"], variables, time, state); end
    if op == "POW_INT"; return expression_value(node["base"], variables, time, state)^node["exponent"]; end
    if op in ("EXP", "LOG", "SIN", "COS", "SQRT")
        argument = expression_value(node["argument"], variables, time, state)
        return Dict("EXP"=>exp, "LOG"=>log, "SIN"=>sin, "COS"=>cos, "SQRT"=>sqrt)[op](argument)
    end
    left = expression_value(node["left"], variables, time, state)
    right = expression_value(node["right"], variables, time, state)
    if op == "ADD"; return left + right; end
    if op == "SUB"; return left - right; end
    if op == "MUL"; return left * right; end
    if op == "DIV"; ensure(right != 0, "NUMERICAL_ZERO_DIVISOR"); return left / right; end
    fail("NUMERICAL_EXPRESSION", op)
end

function rational_value(text)
    pieces = split(string(text), "/")
    ensure(length(pieces) in (1, 2), "RATIONAL_SYNTAX")
    numerator = parse(BigInt, pieces[1])
    denominator = length(pieces) == 1 ? BigInt(1) : parse(BigInt, pieces[2])
    ensure(denominator != 0, "ZERO_DENOMINATOR")
    numerator // denominator
end

struct RationalInterval
    lower::Rational{BigInt}
    upper::Rational{BigInt}
    function RationalInterval(lower, upper)
        ensure(lower <= upper, "INTERVAL_ORDER")
        new(lower, upper)
    end
end

interval_dict(value::RationalInterval) = Dict{String,Any}("kind"=>"RATIONAL_INTERVAL", "lower"=>string(numerator(value.lower)) * (denominator(value.lower) == 1 ? "" : "/" * string(denominator(value.lower))), "upper"=>string(numerator(value.upper)) * (denominator(value.upper) == 1 ? "" : "/" * string(denominator(value.upper))))

function rational_power(value::RationalInterval, exponent)
    ensure(exponent isa Integer && abs(exponent) <= 32, "INTERVAL_POWER")
    if exponent < 0
        ensure(!(value.lower <= 0 <= value.upper), "INTERVAL_ZERO_DIVISOR")
        positive = rational_power(value, -exponent)
        return RationalInterval(1 // positive.upper, 1 // positive.lower)
    elseif exponent == 0
        return RationalInterval(1 // 1, 1 // 1)
    end
    candidates = [value.lower^exponent, value.upper^exponent]
    if iseven(exponent) && value.lower <= 0 <= value.upper; push!(candidates, 0 // 1); end
    RationalInterval(minimum(candidates), maximum(candidates))
end

struct BigFloatInterval
    lower::BigFloat
    upper::BigFloat
    precision_digits::Int
    function BigFloatInterval(lower, upper, precision_digits)
        ensure(isfinite(lower) && isfinite(upper) && lower <= upper, "DECIMAL_INTERVAL")
        ensure(2 <= precision_digits <= 771, "DECIMAL_PRECISION")
        new(lower, upper, precision_digits)
    end
end

decimal_bits(digits) = min(2560, ceil(Int, digits * log2(10)))

function decimal_decode(row)
    digits = Int(row["precision_digits"])
    bits = decimal_bits(digits)
    lower = setprecision(BigFloat, bits) do
        setrounding(BigFloat, RoundDown) do; parse(BigFloat, row["lower"]); end
    end
    upper = setprecision(BigFloat, bits) do
        setrounding(BigFloat, RoundUp) do; parse(BigFloat, row["upper"]); end
    end
    BigFloatInterval(lower, upper, digits)
end

function rounded(binary, left, right, mode, digits)
    setprecision(BigFloat, decimal_bits(digits)) do
        setrounding(BigFloat, mode) do; binary(BigFloat(left), BigFloat(right)); end
    end
end

function decimal_binary(operation, left::BigFloatInterval, right::BigFloatInterval)
    digits = min(left.precision_digits, right.precision_digits)
    if operation == "ADD"
        return BigFloatInterval(rounded(+, left.lower, right.lower, RoundDown, digits), rounded(+, left.upper, right.upper, RoundUp, digits), digits)
    elseif operation == "SUB"
        return BigFloatInterval(rounded(-, left.lower, right.upper, RoundDown, digits), rounded(-, left.upper, right.lower, RoundUp, digits), digits)
    end
    if operation == "DIV"; ensure(!(right.lower <= 0 <= right.upper), "INTERVAL_ZERO_DIVISOR"); end
    binary = operation == "MUL" ? (*) : operation == "DIV" ? (/) : fail("INTERVAL_OPERATION")
    lows = [rounded(binary, a, b, RoundDown, digits) for a in (left.lower,left.upper), b in (right.lower,right.upper)]
    highs = [rounded(binary, a, b, RoundUp, digits) for a in (left.lower,left.upper), b in (right.lower,right.upper)]
    BigFloatInterval(minimum(lows), maximum(highs), digits)
end

function decimal_power(value::BigFloatInterval, exponent)
    ensure(exponent isa Integer && abs(exponent) <= 32, "INTERVAL_POWER")
    if exponent < 0
        ensure(!(value.lower <= 0 <= value.upper), "INTERVAL_ZERO_DIVISOR")
        positive = decimal_power(value, -exponent)
        one = BigFloatInterval(BigFloat(1), BigFloat(1), value.precision_digits)
        return decimal_binary("DIV", one, positive)
    elseif exponent == 0
        return BigFloatInterval(BigFloat(1), BigFloat(1), value.precision_digits)
    end
    bits = decimal_bits(value.precision_digits)
    lows = [setprecision(BigFloat, bits) do; setrounding(BigFloat, RoundDown) do; BigFloat(endpoint)^exponent; end; end for endpoint in (value.lower,value.upper)]
    highs = [setprecision(BigFloat, bits) do; setrounding(BigFloat, RoundUp) do; BigFloat(endpoint)^exponent; end; end for endpoint in (value.lower,value.upper)]
    if iseven(exponent) && value.lower <= 0 <= value.upper; push!(lows, BigFloat(0)); push!(highs, BigFloat(0)); end
    BigFloatInterval(minimum(lows), maximum(highs), value.precision_digits)
end

function interval_control(spec)
    ensure(spec["schema_id"] == "IntervalCertificateV1" && spec["arithmetic"] in ("EXACT_RATIONAL", "DECIMAL_DIRECTED"), "INTERVAL_CERTIFICATE_SCHEMA")
    rational_decode(row) = RationalInterval(rational_value(row["lower"]), rational_value(row["upper"]))
    decode = spec["arithmetic"] == "EXACT_RATIONAL" ? rational_decode : decimal_decode
    values = Dict(name => decode(row) for (name, row) in spec["inputs"])
    for step in spec["steps"]
        operation = step["operation"]
        if operation == "POW_INT"
            parent = values[step["parents"][1]]
            result = parent isa RationalInterval ? rational_power(parent, step["parameters"]["exponent"]) : decimal_power(parent, step["parameters"]["exponent"])
        else
            left, right = values[step["parents"][1]], values[step["parents"][2]]
            if left isa BigFloatInterval
                result = decimal_binary(operation, left, right)
            else
                candidates = [a*b for a in (left.lower,left.upper), b in (right.lower,right.upper)]
                result = if operation == "ADD"
                    RationalInterval(left.lower + right.lower, left.upper + right.upper)
                elseif operation == "SUB"
                    RationalInterval(left.lower - right.upper, left.upper - right.lower)
                elseif operation == "MUL"
                    RationalInterval(minimum(candidates), maximum(candidates))
                elseif operation == "DIV"
                    ensure(!(right.lower <= 0 <= right.upper), "INTERVAL_ZERO_DIVISOR")
                    quotients = [a/b for a in (left.lower,left.upper), b in (right.lower,right.upper)]
                    RationalInterval(minimum(quotients), maximum(quotients))
                else
                    fail("INTERVAL_OPERATION")
                end
            end
        end
        values[step["id"]] = result
    end
    output = values[spec["output"]["value_id"]]
    claimed = decode(spec["output"]["claimed_enclosure"])
    ensure(claimed.lower <= output.lower && output.upper <= claimed.upper, "INTERVAL_CERTIFICATE_MISMATCH")
    claimed_dict = Dict{String,Any}(String(key)=>value for (key,value) in spec["output"]["claimed_enclosure"])
    Dict{String,Any}("schema_id"=>"JuliaIntervalReceiptV1", "status"=>"VERIFIED_ENCLOSURE", "certificate_hash"=>domain_digest(spec,"IntervalCertificateV1"), "enclosure"=>claimed_dict, "scientific_promotion"=>false)
end

function ode_control(spec)
    ensure(spec["schema_id"] == "DeclarativeOdeSpecV1" && spec["system_kind"] in ("ODE", "RGE"), "ODE_SPEC_SCHEMA")
    initial = parse.(Float64, spec["initial_state"])
    parameters = Dict(name => parse(Float64, value) for (name, value) in spec["parameters"])
    expressions = spec["rhs"]
    ensure(length(expressions) == length(initial), "ODE_RHS_ARITY")
    function rhs!(du, u, p, t)
        for index in eachindex(expressions)
            du[index] = expression_value(expressions[index], parameters, t, u)
        end
    end
    t0, t1 = parse(Float64, spec["initial_time"]), parse(Float64, spec["final_time"])
    problem = ODEProblem(rhs!, initial, (t0, t1))
    solution = solve(problem, Vern9(), reltol=parse(Float64, spec["rtol"]), abstol=parse(Float64, spec["atol"]), saveat=[t1])
    final_state = solution.u[end]
    ensure(all(isfinite, final_state), "ODE_SOLVER_FAILURE")
    return Dict{String,Any}(
        "schema_id" => "JuliaNumericalRunReceiptV1", "system_kind" => spec["system_kind"],
        "solver" => "OrdinaryDiffEq.Vern9", "specification_hash" => domain_digest(spec, "DeclarativeOdeSpecV1"),
        "final_time" => @sprintf("%.17g", t1), "final_state" => [@sprintf("%.17g", value) for value in final_state],
        "arbitrary_callback_executed" => false, "scientific_promotion" => false,
    )
end

const SOBOL_BITS = 32
const SOBOL_TABLE = "VPC_SOBOL_2D_BRATLEY_FOX_BASE_V1"

function directions(axis)
    values = UInt32[UInt32(1) << (SOBOL_BITS - index) for index in 1:SOBOL_BITS]
    if axis == 2
        for index in 2:SOBOL_BITS
            values[index] = values[index - 1] ⊻ (values[index - 1] >> 1)
        end
    end
    values
end

function sobol_points(sample_count, dimension, seed, scrambling)
    ensure(1 <= dimension <= 2 && 1 <= sample_count <= 1_048_576, "SOBOL_DOMAIN")
    dirs = [directions(axis) for axis in 1:dimension]
    shifts = UInt32[]
    for axis in 0:(dimension - 1)
        if scrambling == "NONE"
            push!(shifts, UInt32(0))
        else
            material = Vector{UInt8}(codeunits("VPC_SOBOL_SHIFT_V1\0$(seed)\0$(axis)"))
            bytes = sha256(material)
            push!(shifts, (UInt32(bytes[1]) << 24) | (UInt32(bytes[2]) << 16) | (UInt32(bytes[3]) << 8) | UInt32(bytes[4]))
        end
    end
    points = Vector{Vector{UInt32}}()
    for index in 0:(sample_count - 1)
        gray = UInt32(index ⊻ (index >> 1))
        row = UInt32[]
        for axis in 1:dimension
            value, bits, bit = UInt32(0), gray, 1
            while bits != 0
                if (bits & UInt32(1)) != 0; value = value ⊻ dirs[axis][bit]; end
                bits >>= 1; bit += 1
            end
            push!(row, value ⊻ shifts[axis])
        end
        push!(points, row)
    end
    points
end

function point_hash(points)
    context = SHA.SHA2_256_CTX()
    update!(context, Vector{UInt8}(codeunits("VPC_SOBOL_UINT32_INPUT_SET_v1\0")))
    for row in points, value in row
        update!(context, UInt8[(value >> 24) & 0xff, (value >> 16) & 0xff, (value >> 8) & 0xff, value & 0xff])
    end
    bytes2hex(digest!(context))
end

function qmc_control(spec)
    ensure(spec["schema_id"] == "QMCEnsembleSpecV1" && spec["generator_family"] == "SOBOL" && spec["specification_version"] == "VPC_SOBOL_UINT32_V1" && spec["direction_table"] == SOBOL_TABLE, "QMC_SPEC_SCHEMA")
    variables = String.(spec["variables"])
    bounds = [(parse(Float64, row[1]), parse(Float64, row[2])) for row in spec["bounds"]]
    points = sobol_points(spec["sample_count"], length(variables), spec["seed"], spec["scrambling"])
    samples = Float64[]
    for row in points
        values = Dict(variables[index] => bounds[index][1] + (bounds[index][2] - bounds[index][1]) * Float64(row[index]) / 2.0^32 for index in eachindex(variables))
        push!(samples, expression_value(spec["integrand"], values, 0.0, Float64[]))
    end
    mean_value = sum(samples) / length(samples)
    variance_value = sum((value - mean_value)^2 for value in samples) / length(samples)
    return Dict{String,Any}(
        "schema_id" => "JuliaQMCReceiptV1", "semantics" => "SAMPLED_DISTRIBUTION_ESTIMATE",
        "specification_hash" => domain_digest(spec, "QMCEnsembleSpecV1"), "generated_input_set_sha256" => point_hash(points),
        "mean" => @sprintf("%.17g", mean_value), "variance" => @sprintf("%.17g", variance_value),
        "scientific_promotion" => false,
    )
end

function covariance_control(spec)
    ensure(spec["schema_id"] == "CovariancePropagationSpecV1", "COVARIANCE_SPEC_SCHEMA")
    variables = String.(spec["variables"])
    mean_values = [parse(Float64, spec["mean"][name]) for name in variables]
    expressions = spec["outputs"]
    evaluate(values) = [expression_value(expression, Dict(variables[index] => values[index] for index in eachindex(variables)), 0.0, Float64[]) for expression in expressions]
    base = evaluate(mean_values)
    jacobian = zeros(length(base), length(variables))
    for column in eachindex(variables)
        step = sqrt(eps(Float64)) * max(abs(mean_values[column]), 1.0)
        plus, minus = copy(mean_values), copy(mean_values)
        plus[column] += step; minus[column] -= step
        jacobian[:, column] = (evaluate(plus) - evaluate(minus)) / (2step)
    end
    covariance = [parse(Float64, spec["covariance"][i][j]) for i in eachindex(variables), j in eachindex(variables)]
    output_covariance = jacobian * covariance * transpose(jacobian)
    return Dict{String,Any}(
        "schema_id" => "JuliaCovarianceReceiptV1", "semantics" => "LOCAL_LINEAR_COVARIANCE",
        "specification_hash" => domain_digest(spec, "CovariancePropagationSpecV1"),
        "output_mean" => [@sprintf("%.17g", value) for value in base],
        "jacobian" => [[@sprintf("%.17g", jacobian[i,j]) for j in axes(jacobian,2)] for i in axes(jacobian,1)],
        "output_covariance" => [[@sprintf("%.17g", output_covariance[i,j]) for j in axes(output_covariance,2)] for i in axes(output_covariance,1)],
        "scientific_promotion" => false,
    )
end

function main(args)
    ensure(length(args) == 2, "USAGE: KIND SPEC_JSON")
    kind, spec = args[1], JSON3.read(read(args[2], String), Dict{String,Any})
    result = kind == "interval" ? interval_control(spec) : kind == "ode" ? ode_control(spec) : kind == "qmc" ? qmc_control(spec) : kind == "covariance" ? covariance_control(spec) : fail("NUMERICAL_CONTROL_KIND")
    println(canonical_json(result))
end

try
    main(ARGS)
catch exception
    println(stderr, "REJECTED:", sprint(showerror, exception))
    exit(2)
end
