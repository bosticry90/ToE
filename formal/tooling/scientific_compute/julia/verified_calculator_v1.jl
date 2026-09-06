#!/usr/bin/env julia

# Independent exact evaluator for the Verified Physics Calculator v1.
# It consumes only frozen contracts, source artifacts, and a candidate packet;
# it does not import or call any Python or historical physics routine.

using JSON3
using Nemo
using SHA

const VERIFIER_ID = "julia-nemo-verified-calculator-v1"
const ALLOWED_OPS = Set(["SOURCE_DECODE", "LITERAL", "OUTPUT_BIND", "ADD", "SUB", "MUL", "DIV", "NEG", "POW_INT", "MAKE_TENSOR", "INDEX", "MATMUL", "EQUAL", "ALL", "SELECT", "CLASSIFY_ZERO"])

fail(code, detail="") = error(isempty(detail) ? code : string(code, ":", detail))
ensure(test, code, detail="") = test ? nothing : fail(code, detail)

function parse_fraction(text)
    ensure(text isa String || text isa Integer, "FRACTION_SYNTAX")
    pieces = split(string(text), "/")
    ensure(length(pieces) in (1, 2), "FRACTION_SYNTAX")
    numerator = parse(BigInt, pieces[1])
    denominator = length(pieces) == 1 ? BigInt(1) : parse(BigInt, pieces[2])
    ensure(denominator != 0, "ZERO_DENOMINATOR")
    return QQ(numerator, denominator)
end

function field_runtime(spec)
    if spec["field_id"] == "RATIONAL_FIELD"
        return (QQ, nothing)
    end
    polynomial_ring_q, generator = polynomial_ring(QQ, "_vpc_alpha")
    polynomial = zero(polynomial_ring_q)
    for (power, coefficient) in enumerate(spec["minimal_polynomial"])
        polynomial += parse_fraction(coefficient) * generator^(power - 1)
    end
    ensure(is_irreducible(polynomial), "MINIMAL_POLYNOMIAL_REDUCIBLE")
    number_field_q, alpha = number_field(polynomial, spec["primitive_element"])
    return (number_field_q, alpha)
end

struct ExactContext
    coefficient_field
    alpha
    polynomial_ring
    fraction_field
    variables
    symbols::Vector{String}
    degree::Int
end

function exact_context(profile)
    coefficient_field, alpha = field_runtime(profile["algebraic_field"])
    symbols = String.(profile["symbols"])
    ring_symbols = isempty(symbols) ? ["_vpc_constant"] : symbols
    polynomial_ring_k, variables = polynomial_ring(coefficient_field, ring_symbols)
    fraction_field_k = fraction_field(polynomial_ring_k)
    degree = length(profile["algebraic_field"]["minimal_polynomial"]) - 1
    return ExactContext(coefficient_field, alpha, polynomial_ring_k, fraction_field_k, variables, symbols, degree)
end

function coefficient_value(context::ExactContext, coordinates)
    ensure(length(coordinates) == context.degree, "ALGEBRAIC_COORDINATES")
    if context.alpha === nothing
        return parse_fraction(coordinates[1])
    end
    value = zero(context.coefficient_field)
    for (power, coefficient) in enumerate(coordinates)
        value += context.coefficient_field(parse_fraction(coefficient)) * context.alpha^(power - 1)
    end
    return value
end

function polynomial_value(context::ExactContext, spec)
    ensure(Set(keys(spec)) == Set(["terms"]), "POLYNOMIAL_SCHEMA")
    output = zero(context.polynomial_ring)
    for term in spec["terms"]
        powers = term["powers"]
        ensure(length(powers) == length(context.symbols), "POLYNOMIAL_POWERS")
        monomial = one(context.polynomial_ring)
        for (index, power) in enumerate(powers)
            ensure(power isa Integer && power >= 0, "POLYNOMIAL_POWERS")
            monomial *= context.variables[index]^power
        end
        output += coefficient_value(context, term["coefficient"]) * monomial
    end
    return output
end

struct TensorValue
    shape::Vector{Int}
    entries::Vector{Any}
end

struct AtomValue
    atom_type::String
    value::String
end

function decode_exact(context::ExactContext, spec)
    kind = spec["kind"]
    if kind == "RATIONAL_FUNCTION"
        ensure(String.(spec["symbols"]) == context.symbols, "SYMBOL_TABLE")
        numerator = polynomial_value(context, spec["numerator"])
        denominator = polynomial_value(context, spec["denominator"])
        ensure(!iszero(denominator), "ZERO_DENOMINATOR")
        return context.fraction_field(numerator) / context.fraction_field(denominator)
    end
    if kind == "BOOLEAN"
        ensure(spec["value"] isa Bool, "EXACT_BOOLEAN")
        return spec["value"]
    elseif kind == "ATOM"
        return AtomValue(spec["atom_type"], spec["value"])
    end
    ensure(kind == "TENSOR", "EXACT_VALUE_KIND")
    shape = Int.(spec["shape"])
    entries = Any[decode_exact(context, item) for item in spec["entries"]]
    ensure(prod(shape) == length(entries), "TENSOR_ENTRY_COUNT")
    return TensorValue(shape, entries)
end

function exact_equal(left, right)
    if left isa TensorValue || right isa TensorValue
        return left isa TensorValue && right isa TensorValue && left.shape == right.shape && all(exact_equal(a, b) for (a, b) in zip(left.entries, right.entries))
    end
    if left isa AtomValue || right isa AtomValue
        return left isa AtomValue && right isa AtomValue && left.atom_type == right.atom_type && left.value == right.value
    end
    return left == right
end

function elementwise(op, left, right)
    scalar = op == "ADD" ? (+) : op == "SUB" ? (-) : (*)
    if !(left isa TensorValue) && !(right isa TensorValue)
        return scalar(left, right)
    elseif left isa TensorValue && right isa TensorValue
        ensure(left.shape == right.shape, "TENSOR_SHAPE")
        return TensorValue(left.shape, Any[scalar(a, b) for (a, b) in zip(left.entries, right.entries)])
    else
        ensure(op == "MUL", "SCALAR_TENSOR_OPERATION")
        tensor, value = left isa TensorValue ? (left, right) : (right, left)
        return TensorValue(tensor.shape, Any[item * value for item in tensor.entries])
    end
end

function matrix_multiply(left::TensorValue, right::TensorValue)
    ensure(length(left.shape) == 2 && length(right.shape) == 2 && left.shape[2] == right.shape[1], "MATRIX_SHAPE")
    rows, common, columns = left.shape[1], left.shape[2], right.shape[2]
    entries = Any[]
    for i in 1:rows, j in 1:columns
        value = zero(left.entries[1] * right.entries[1])
        for k in 1:common
            value += left.entries[(i - 1) * common + k] * right.entries[(k - 1) * columns + j]
        end
        push!(entries, value)
    end
    return TensorValue([rows, columns], entries)
end

function json_pointer(document, pointer::String)
    isempty(pointer) && return document
    ensure(startswith(pointer, "/"), "JSON_POINTER_SYNTAX")
    value = document
    for encoded in split(pointer[2:end], "/")
        key = replace(replace(encoded, "~1" => "/"), "~0" => "~")
        if value isa Dict
            ensure(haskey(value, key), "SOURCE_LOCATOR_NOT_FOUND", pointer)
            value = value[key]
        elseif value isa Vector
            index = parse(Int, key) + 1
            ensure(1 <= index <= length(value), "SOURCE_LOCATOR_NOT_FOUND", pointer)
            value = value[index]
        else
            fail("SOURCE_LOCATOR_NOT_FOUND", pointer)
        end
    end
    return value
end

function resolve_source(reference, declarations, source_root)
    path = reference["artifact_path"]
    rows = [row for row in declarations if row["path"] == path]
    ensure(length(rows) == 1 && rows[1]["sha256"] == reference["artifact_sha256"], "SOURCE_NOT_ALLOWLISTED", path)
    full = normpath(joinpath(source_root, split(path, '/')...))
    relative = relpath(abspath(full), abspath(source_root))
    ensure(relative != ".." && !startswith(relative, ".." * string(Base.Filesystem.path_separator)), "SOURCE_PATH_ESCAPE")
    raw = read(full)
    ensure(bytes2hex(sha256(raw)) == rows[1]["sha256"] && length(raw) == rows[1]["byte_size"], "SOURCE_IDENTITY_MISMATCH")
    document = JSON3.read(String(raw), Dict{String,Any})
    kind = reference["type"]
    if kind == "JsonPointerValueRef"
        return json_pointer(document, reference["pointer"])
    elseif kind == "TensorComponentRef"
        value = json_pointer(document, reference["pointer"])
        for index in reference["indices"]
            value = value[index + 1]
        end
        return value
    elseif kind == "NamedConventionRef"
        return json_pointer(document, reference["conventions_pointer"])[reference["name"]]
    elseif kind == "UniqueTableCellRef"
        rows = json_pointer(document, reference["table_pointer"])
        matches = [row for row in rows if get(row, reference["match_field"], nothing) == reference["match_value"]]
        ensure(length(matches) == 1, "SOURCE_SELECTION_NOT_UNIQUE")
        return json_pointer(matches[1], reference["value_pointer"])
    end
    fail("SOURCE_REFERENCE_TYPE")
end

include("verified_calculator_c03_rv_v1.jl")

function topological_nodes(candidate)
    nodes = Dict(row["node_id"] => row for row in candidate["graph"]["nodes"])
    ensure(length(nodes) == length(candidate["graph"]["nodes"]), "DUPLICATE_NODE")
    edges = Set((edge[1], edge[2]) for edge in candidate["graph"]["edges"])
    expected = Set((parent, node["node_id"]) for node in values(nodes) for parent in node["parents"])
    ensure(edges == expected, "PARENT_EDGE_DISAGREEMENT")
    order = String[]
    pending = Set(keys(nodes))
    while !isempty(pending)
        ready = sort([identity for identity in pending if all(parent in order for parent in nodes[identity]["parents"])])
        ensure(!isempty(ready), "CYCLIC_OR_MISSING_PARENT")
        append!(order, ready)
        foreach(identity -> delete!(pending, identity), ready)
    end
    return nodes, order
end

function evaluate_candidate(profile, request, candidate, source_root)
    context = exact_context(profile)
    nodes, order = topological_nodes(candidate)
    ensure(Set(candidate["claimed_outputs"] |> keys) == Set(profile["output_roots"]), "OUTPUT_ROOT_SET")
    ensure(Set(node["operation"] for node in values(nodes)) <= ALLOWED_OPS, "UNKNOWN_OPERATION")
    source_bindings = Dict(row["node_id"] => row["reference"] for row in candidate["source_bindings"])
    values_by_id = Dict{String,Any}()
    for identity in order
        node = nodes[identity]
        op = node["operation"]
        parents = Any[values_by_id[parent] for parent in node["parents"]]
        value = if op == "SOURCE_DECODE"
            ensure(haskey(source_bindings, identity) && node["parameters"]["reference"] == source_bindings[identity], "SOURCE_BINDING_MISMATCH")
            decode_exact(context, resolve_source(node["parameters"]["reference"], profile["source_declarations"], source_root))
        elseif op == "LITERAL"
            decode_exact(context, node["claimed_value"])
        elseif op == "OUTPUT_BIND"
            ensure(length(parents) == 1, "OUTPUT_BIND_ARITY"); parents[1]
        elseif op in ("ADD", "SUB", "MUL")
            ensure(length(parents) == 2, "BINARY_ARITY"); elementwise(op, parents[1], parents[2])
        elseif op == "DIV"
            ensure(length(parents) == 2 && !(parents[1] isa TensorValue) && !(parents[2] isa TensorValue), "DIV_SCALAR_ONLY"); parents[1] / parents[2]
        elseif op == "NEG"
            ensure(length(parents) == 1, "NEG_ARITY"); parents[1] isa TensorValue ? TensorValue(parents[1].shape, Any[-item for item in parents[1].entries]) : -parents[1]
        elseif op == "POW_INT"
            ensure(length(parents) == 1 && !(parents[1] isa TensorValue), "POWER_SCALAR_ONLY"); parents[1]^node["parameters"]["exponent"]
        elseif op == "MAKE_TENSOR"
            TensorValue(Int.(node["parameters"]["shape"]), parents)
        elseif op == "INDEX"
            tensor = parents[1]; ensure(tensor isa TensorValue, "INDEX_TENSOR")
            flat = 0
            for (index, size) in zip(node["parameters"]["indices"], tensor.shape); flat = flat * size + index; end
            tensor.entries[flat + 1]
        elseif op == "MATMUL"
            matrix_multiply(parents[1], parents[2])
        elseif op == "EQUAL"
            ensure(length(parents) == 2, "EQUAL_ARITY"); exact_equal(parents[1], parents[2])
        elseif op == "ALL"
            ensure(!isempty(parents) && all(item isa Bool for item in parents), "ALL_BOOLEAN_ONLY"); all(parents)
        elseif op == "SELECT"
            ensure(length(parents) == 3 && parents[1] isa Bool, "SELECT_SIGNATURE"); parents[1] ? parents[2] : parents[3]
        elseif op == "CLASSIFY_ZERO"
            ensure(length(parents) == 1, "CLASSIFY_ZERO_ARITY")
            value = parents[1]
            iszero_value = value isa TensorValue ? all(iszero, value.entries) : iszero(value)
            AtomValue("ENUM", iszero_value ? "EVALUATED_ZERO" : "EVALUATED_NONZERO")
        else
            fail("UNKNOWN_OPERATION", op)
        end
        claimed = decode_exact(context, node["claimed_value"])
        ensure(exact_equal(value, claimed), "RECOMPUTATION_MISMATCH", identity)
        values_by_id[identity] = value
    end
    for root in profile["output_roots"]
        ensure(haskey(nodes, root) && nodes[root]["operation"] == "OUTPUT_BIND", "OUTPUT_BINDING")
        ensure(exact_equal(values_by_id[root], decode_exact(context, candidate["claimed_outputs"][root])), "EMITTED_ROOT_MISMATCH", root)
    end
    return context
end

function json_escape(value::String)
    # Exact-IR identities are ASCII. JSON3 supplies correct JSON string escaping.
    return String(JSON3.write(value))
end

function canonical_json(value)
    if value === nothing
        return "null"
    elseif value isa Bool
        return value ? "true" : "false"
    elseif value isa Integer
        return string(value)
    elseif value isa String
        return json_escape(value)
    elseif value isa Vector
        return "[" * join(canonical_json.(value), ",") * "]"
    elseif value isa Dict
        keys_sorted = sort(String.(collect(keys(value))))
        return "{" * join([json_escape(key) * ":" * canonical_json(value[key]) for key in keys_sorted], ",") * "}"
    end
    fail("CANONICAL_JSON_TYPE", string(typeof(value)))
end

function domain_digest(value, domain)
    material = Vector{UInt8}(codeunits(domain * "\0" * canonical_json(value)))
    return bytes2hex(sha256(material))
end

function main(args)
    ensure(length(args) == 5, "USAGE: PROFILE POLICY REQUEST CANDIDATE SOURCE_ROOT")
    profile = JSON3.read(read(args[1], String), Dict{String,Any})
    policy = JSON3.read(read(args[2], String), Dict{String,Any})
    request = JSON3.read(read(args[3], String), Dict{String,Any})
    candidate = JSON3.read(read(args[4], String), Dict{String,Any})
    source_root = args[5]
    ensure(policy["julia_verifier"] == VERIFIER_ID, "JULIA_VERIFIER_ID")
    ensure(domain_digest(profile, "PhysicsProfileV1") == request["physics_profile_hash"], "JULIA_REQUEST_PROFILE_HASH")
    ensure(domain_digest(policy, "VerificationPolicyV1") == request["verification_policy_hash"], "JULIA_REQUEST_POLICY_HASH")
    ensure(domain_digest(request, "CalculationRequestV1:computation") == candidate["computation_id"], "JULIA_CANDIDATE_COMPUTATION_ID")
    ensure(Set(String.(request["requested_roots"])) == Set(String.(profile["output_roots"])), "JULIA_REQUEST_ROOTS")
    if profile["profile_id"] == "C03_RV_SU5_EXACT_PROFILE_v1"
        evaluate_c03_rv_candidate(profile, request, candidate, source_root)
    else
        evaluate_candidate(profile, request, candidate, source_root)
    end
    output_hashes = Dict(root => domain_digest(candidate["claimed_outputs"][root], "ExactOutputValueV1") for root in profile["output_roots"])
    receipt = Dict{String,Any}(
        "schema_id" => "JuliaIndependentEvidenceV1",
        "verifier_id" => VERIFIER_ID,
        "computation_id" => candidate["computation_id"],
        "candidate_hash" => domain_digest(candidate, "CandidatePacketV1"),
        "output_value_hashes" => output_hashes,
        "shared_physics_routines" => false,
        "arbitrary_code_from_candidate_executed" => false,
        "scientific_promotion" => false,
    )
    println(canonical_json(receipt))
end

try
    main(ARGS)
catch exception
    println(stderr, "REJECTED:", sprint(showerror, exception, catch_backtrace()))
    exit(2)
end
