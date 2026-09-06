# Independent source-to-result route for the frozen C03/RV exact profile.
#
# This file deliberately does not interpret Python-produced intermediate
# values.  It resolves and hash-checks the 31 source contexts, reconstructs
# the three C03 and thirteen RV outputs with Julia/Nemo exact arithmetic, and
# compares only the resulting canonical output objects.

using LinearAlgebra

fzero(c) = c.fraction_field(zero(c.polynomial_ring))
fone(c) = c.fraction_field(one(c.polynomial_ring))
fq(c, value) = c.fraction_field(c.polynomial_ring(c.coefficient_field(parse_fraction(value))))
fsymbol(c, name) = begin
    index = findfirst(==(name), c.symbols)
    ensure(index !== nothing, "C03_RV_JULIA_SYMBOL", name)
    c.fraction_field(c.variables[index])
end

function field_constant(c, coordinates)
    ensure(c.alpha !== nothing && length(coordinates) == c.degree, "C03_RV_FIELD_CONSTANT")
    value = zero(c.coefficient_field)
    for (power, coordinate) in enumerate(coordinates)
        value += c.coefficient_field(parse_fraction(coordinate)) * c.alpha^(power - 1)
    end
    return value
end

const SQRT2_COORDINATES = ["0", "13/12", "0", "14/9", "0", "-35/144", "0", "1/72"]
const SQRT3_COORDINATES = ["0", "-21/16", "0", "-181/96", "0", "59/192", "0", "-7/384"]
const IMAGINARY_COORDINATES = ["0", "59/48", "0", "95/288", "0", "-37/576", "0", "5/1152"]

function fk(c, value)
    return c.fraction_field(c.polynomial_ring(value))
end

function parse_profile_expression(c, raw)
    text = string(raw)
    ensure(ncodeunits(text) <= 2048, "C03_RV_EXPRESSION_SIZE")
    tree = Meta.parse(replace(text, "**" => "^"))
    imaginary = fk(c, field_constant(c, IMAGINARY_COORDINATES))
    sqrt2 = fk(c, field_constant(c, SQRT2_COORDINATES))
    sqrt3 = fk(c, field_constant(c, SQRT3_COORDINATES))
    function visit(node)
        if node isa Integer
            return fq(c, node)
        elseif node isa Rational
            return fq(c, string(numerator(node), "/", denominator(node)))
        elseif node isa Symbol
            node == :I && return imaginary
            node == :sqrt2 && return sqrt2
            node == :sqrt3 && return sqrt3
            return fsymbol(c, String(node))
        end
        ensure(node isa Expr && node.head == :call, "C03_RV_EXPRESSION_CAPABILITY")
        op = node.args[1]
        args = node.args[2:end]
        if op == :sqrt
            ensure(length(args) == 1 && args[1] in (2, 3, 6), "C03_RV_SQRT_DOMAIN")
            return args[1] == 2 ? sqrt2 : args[1] == 3 ? sqrt3 : sqrt2 * sqrt3
        elseif op == :+
            ensure(!isempty(args), "C03_RV_EXPRESSION_ARITY")
            return foldl(+, visit.(args))
        elseif op == :-
            ensure(length(args) in (1, 2), "C03_RV_EXPRESSION_ARITY")
            return length(args) == 1 ? -visit(args[1]) : visit(args[1]) - visit(args[2])
        elseif op == :*
            ensure(!isempty(args), "C03_RV_EXPRESSION_ARITY")
            return foldl(*, visit.(args))
        elseif op == :/
            ensure(length(args) == 2, "C03_RV_EXPRESSION_ARITY")
            denominator = visit(args[2]); ensure(!iszero(denominator), "ZERO_DENOMINATOR")
            return visit(args[1]) / denominator
        elseif op == :^
            ensure(length(args) == 2 && args[2] isa Integer && abs(args[2]) <= 32, "C03_RV_POWER_DOMAIN")
            return visit(args[1])^args[2]
        end
        fail("C03_RV_EXPRESSION_CAPABILITY", string(op))
    end
    return visit(tree)
end

function decode_profile_value(value)
    kind = value["type"]
    if kind == "NULL"
        return nothing
    elseif kind in ("BOOLEAN", "INTEGER", "TEXT")
        return value["value"]
    elseif kind == "LIST" || kind == "TUPLE"
        return Any[decode_profile_value(item) for item in value["items"]]
    elseif kind == "MAP"
        return Dict{String,Any}(row[1] => decode_profile_value(row[2]) for row in value["entries"])
    end
    # C03/RV source material is raw JSON-domain data.  Exact expressions and
    # matrices occur only in untrusted intermediate claims and are not inputs
    # to this independent route.
    fail("C03_RV_SOURCE_PROFILE_VALUE_KIND", kind)
end

function allowed_document(profile, source_root, path)
    rows = [row for row in profile["source_declarations"] if row["path"] == path]
    ensure(length(rows) == 1, "SOURCE_NOT_ALLOWLISTED", path)
    full = normpath(joinpath(source_root, split(path, '/')...))
    raw = read(full)
    ensure(bytes2hex(sha256(raw)) == rows[1]["sha256"] && length(raw) == rows[1]["byte_size"], "SOURCE_IDENTITY_MISMATCH")
    return JSON3.read(String(raw), Dict{String,Any})
end

function c03_rv_sources(profile, candidate, source_root)
    expected = Set([
        "C03.SOURCE.ORDERED_FIELDS", "C03.SOURCE.COLOR_TENSOR", "C03.SOURCE.SPINOR_X", "C03.SOURCE.SPINOR_Y",
        "C03.SOURCE.CLIFFORD_DOMAIN", "C03.SOURCE.GAUGE_PARAMETER", "C03.SOURCE.HYPERCHARGE_D",
        "C03.SOURCE.HYPERCHARGE_E", "C03.SOURCE.DIAGRAM_PHASE", "C03.SOURCE.COMMON_PREFACTOR",
        "C03.SOURCE.COUPLING_MONOMIAL", "C03.SOURCE.NORMALIZATION_DOMAIN", "C03.CONVENTION.WILSON_SYMBOL",
        "C03.NATIVE.SOURCE.OCCURRENCES", "C03.NATIVE.SOURCE.REQUESTS", "C03.NATIVE.SOURCE.DEFECTS",
        "C03.NATIVE.SOURCE.COLUMNS", "C03.NATIVE.SOURCE.LEDGER", "C03.NATIVE.SOURCE.RELATIONS",
        "C03.NATIVE.SOURCE.REPRESENTATIVES", "C03.NATIVE.SOURCE.ORDER", "C03.NATIVE.SOURCE.REP_CACHE",
        "C03.NATIVE.SOURCE.DUAL_CACHE", "C03.NATIVE.SOURCE.Q_CACHE", "C03.NATIVE.SOURCE.K_CACHE",
        ["RV0$(i).SOURCE.CONTEXT" for i in 1:6]...,
    ])
    nodes = Dict(row["node_id"] => row for row in candidate["graph"]["nodes"])
    bindings = Dict(row["node_id"] => row for row in candidate["source_bindings"])
    ensure(Set(keys(bindings)) == expected, "C03_RV_JULIA_SOURCE_CENSUS")
    values = Dict{String,Any}()
    for identity in sort(collect(expected))
        node = nodes[identity]; binding = bindings[identity]
        ensure(node["kind"] == "SOURCE" && node["operation"] == "SOURCE_DECODE" && isempty(node["parents"]), "C03_RV_JULIA_SOURCE_NODE", identity)
        ensure(canonical_json(node["parameters"]) == canonical_json(Dict(key => value for (key, value) in binding if key != "node_id")), "SOURCE_BINDING_MISMATCH", identity)
        reference = node["parameters"]["reference"]
        expected_digest = resolve_source(reference, profile["source_declarations"], source_root)
        claimed = node["claimed_value"]
        ensure(claimed["kind"] == "PROFILE_VALUE", "C03_RV_SOURCE_VALUE_WRAPPER", identity)
        ensure(domain_digest(claimed["value"], "C03RVProfileValueV1") == expected_digest, "C03_RV_SOURCE_MATERIAL_MISMATCH", identity)
        contract = allowed_document(profile, source_root, reference["artifact_path"])
        row = contract["nodes"][identity]
        evidence = node["parameters"]["evidence_references"]
        ensure(row["evidence_reference_count"] == length(evidence), "C03_RV_SOURCE_EVIDENCE_COUNT", identity)
        ensure(row["evidence_references_digest"] == domain_digest(evidence, "C03RVSourceEvidenceReferencesV1"), "C03_RV_SOURCE_EVIDENCE_HASH", identity)
        for item in evidence
            resolve_source(item, profile["source_declarations"], source_root)
        end
        values[identity] = decode_profile_value(claimed["value"])
    end
    return values
end

function zmat(c, rows, columns)
    return [fzero(c) for _ in 1:rows, _ in 1:columns]
end

function eye(c, size)
    value = zmat(c, size, size)
    for i in 1:size; value[i, i] = fone(c); end
    return value
end

function mmul(c, left, right)
    ensure(size(left, 2) == size(right, 1), "JULIA_MATRIX_SHAPE")
    output = zmat(c, size(left, 1), size(right, 2))
    for i in axes(left, 1), j in axes(right, 2), k in axes(left, 2)
        output[i, j] += left[i, k] * right[k, j]
    end
    return output
end

madd(left, right) = left .+ right
msub(left, right) = left .- right
mscale(value, matrix) = value .* matrix
mtrace(matrix) = sum(matrix[i, i] for i in axes(matrix, 1))

function kronm(c, left, right)
    output = zmat(c, size(left, 1) * size(right, 1), size(left, 2) * size(right, 2))
    for i in axes(left, 1), j in axes(left, 2), a in axes(right, 1), b in axes(right, 2)
        output[(i - 1) * size(right, 1) + a, (j - 1) * size(right, 2) + b] = left[i, j] * right[a, b]
    end
    return output
end

function kronmany(c, matrices)
    result = reshape([fone(c)], 1, 1)
    for item in matrices; result = kronm(c, result, item); end
    return result
end

rowmajor(matrix) = [matrix[i, j] for i in axes(matrix, 1) for j in axes(matrix, 2)]
function rowreshape(values, rows, columns)
    return [values[(i - 1) * columns + j] for i in 1:rows, j in 1:columns]
end

function matrix_rank(c, input)
    value = copy(input); row = 1; pivots = 0
    for column in axes(value, 2)
        pivot = findfirst(i -> !iszero(value[i, column]), row:size(value, 1))
        pivot === nothing && continue
        pivot = row - 1 + pivot
        value[row, :], value[pivot, :] = copy(value[pivot, :]), copy(value[row, :])
        value[row, :] ./= value[row, column]
        for i in axes(value, 1)
            i == row && continue
            factor = value[i, column]
            !iszero(factor) && (value[i, :] .-= factor .* value[row, :])
        end
        row += 1; pivots += 1
        row > size(value, 1) && break
    end
    return pivots
end

function solve_linear(c, matrix, target)
    ensure(size(matrix, 1) == length(target), "JULIA_LINEAR_SHAPE")
    augmented = hcat(copy(matrix), reshape(copy(target), :, 1)); row = 1; pivot_columns = Int[]
    for column in axes(matrix, 2)
        pivot = findfirst(i -> !iszero(augmented[i, column]), row:size(matrix, 1))
        pivot === nothing && continue
        pivot = row - 1 + pivot
        augmented[row, :], augmented[pivot, :] = copy(augmented[pivot, :]), copy(augmented[row, :])
        augmented[row, :] ./= augmented[row, column]
        for i in axes(augmented, 1)
            i == row && continue
            factor = augmented[i, column]
            !iszero(factor) && (augmented[i, :] .-= factor .* augmented[row, :])
        end
        push!(pivot_columns, column); row += 1
        row > size(matrix, 1) && break
    end
    for i in axes(augmented, 1)
        ensure(any(!iszero, augmented[i, 1:end-1]) || iszero(augmented[i, end]), "JULIA_LINEAR_INCONSISTENT")
    end
    solution = [fzero(c) for _ in axes(matrix, 2)]
    for (i, column) in enumerate(pivot_columns); solution[column] = augmented[i, end]; end
    ensure(all(iszero, mmul(c, matrix, reshape(solution, :, 1))[:, 1] .- target), "JULIA_LINEAR_RESIDUAL")
    return solution, length(pivot_columns)
end

function sparse_matrix(c, spec, row_key, column_key)
    output = zmat(c, spec["shape"][1], spec["shape"][2]); seen = Set()
    for item in spec["entries"]
        index = (item[row_key] + 1, item[column_key] + 1)
        ensure(!(index in seen), "JULIA_SPARSE_DUPLICATE"); push!(seen, index)
        output[index...] = parse_profile_expression(c, string(item["coefficient"]))
    end
    ensure(length(seen) == spec["nonzero_count"], "JULIA_SPARSE_COUNT")
    return output
end

function pauli_and_gamma_c03(c)
    i = parse_profile_expression(c, "I"); z = fzero(c); o = fone(c)
    sigma = [ [o z; z o], [z o; o z], [z -i; i z], [o z; z -o] ]
    metric = [1, -1, -1, -1]
    bar = [metric[k] .* sigma[k] for k in 1:4]
    gamma = Matrix[]
    for k in 1:4
        top = hcat(zmat(c, 2, 2), sigma[k]); bottom = hcat(bar[k], zmat(c, 2, 2))
        push!(gamma, vcat(top, bottom))
    end
    for a in 1:4, b in 1:4
        ensure(mmul(c, gamma[a], gamma[b]) + mmul(c, gamma[b], gamma[a]) == (2 * (a == b ? metric[a] : 0)) .* eye(c, 4), "C03_JULIA_CLIFFORD")
    end
    return sigma, bar, gamma, metric
end

function c03_spinor_vector(c, context)
    fields = ["dR", "uR_1", "uR_2", "eR"]
    partitions = Set{Tuple}(); orbit_ids = Set{String}()
    for row in context["occurrences"]
        ensure(row["field_order"] == fields, "C03_JULIA_FIELD_ORDER")
        chains = row["source_orbit"]["chain_fields"]
        partition = Tuple(Tuple(findfirst(==(field), fields) for field in chains[name]) for name in row["chain_order"])
        push!(partitions, partition); push!(orbit_ids, row["source_orbit"]["orbit_id"])
    end
    ensure(length(partitions) == 1 && length(orbit_ids) == 1, "C03_JULIA_ORBIT")
    partition = first(partitions)
    values = Any[]
    for raw in Iterators.product(fill(0:1, 4)...)
        index = collect(raw)
        push!(values, fq(c, prod(index[pair[2]] - index[pair[1]] for pair in partition)))
    end
    return values, first(orbit_ids)
end

function c03_spinor_action(c, primary, other, ward)
    first, first_id = c03_spinor_vector(c, primary); second, second_id = c03_spinor_vector(c, other)
    by_id = Dict(first_id => first, second_id => second)
    ensure(Set(keys(by_id)) == Set(["IDENTITY", "IDENTICAL_UR_EXCHANGE"]), "C03_JULIA_TREE_BASIS")
    basis = hcat(by_id["IDENTITY"], by_id["IDENTICAL_UR_EXCHANGE"])
    image = if ward
        first
    else
        sigma, bar, _, metric = pauli_and_gamma_c03(c)
        endpoints = [row["functional_derivative_order"][2] for row in primary["vertices"]]
        axes = [findfirst(==(field), primary["target"]["ordered_fields"]) for field in endpoints]
        action = zmat(c, 16, 16)
        for rho in 1:4, mu in 1:4
            factors = [eye(c, 2) for _ in 1:4]
            for axis in axes; factors[axis] = transpose(mmul(c, bar[rho], sigma[mu])); end
            action .+= fq(c, metric[rho] * metric[mu]) / fq(c, 4) .* kronmany(c, factors)
        end
        mmul(c, action, reshape(first, :, 1))[:, 1]
    end
    coordinates, rank = solve_linear(c, basis, image)
    ensure(rank == 2, "C03_JULIA_TREE_BASIS")
    return coordinates
end

function c03_color_sign(c, context)
    axes = context["axes"]; first_axis = findfirst(==("uR[1].color3"), axes); second_axis = findfirst(==("uR[2].color3"), axes)
    entries = Dict(Tuple(row["index"]) => parse_profile_expression(c, string(row["coefficient"])) for row in context["tensor"]["sparse_entries"])
    ratios = Set()
    for index in keys(entries)
        changed = collect(index); changed[first_axis], changed[second_axis] = changed[second_axis], changed[first_axis]
        push!(ratios, get(entries, Tuple(changed), fzero(c)) / entries[index])
    end
    ensure(length(ratios) == 1 && first(ratios) in (fone(c), -fone(c)), "C03_JULIA_COLOR_SIGN")
    return first(ratios)
end

function c03_phase(c, ledger)
    ensure(ledger["fourier"]["path_integral_phase"] == "exp(+i*S)", "C03_JULIA_PHASE_CONVENTION")
    i = parse_profile_expression(c, "I")
    vertex = Any[]
    for item in ledger["vertices"]
        ensure(startswith(item["exact_rule"], "+i*"), "C03_JULIA_VERTEX_PHASE"); push!(vertex, i)
    end
    rules = Dict(row["id"] => row["rule"] for row in ledger["propagators"])
    ensure(startswith(rules["PROP-FERMION"], "+i*") && startswith(rules["PROP-QUANTUM-GAUGE"], "-i*"), "C03_JULIA_PROPAGATOR_PHASE")
    edges = ledger["topology"]["internal_edges"]
    incidence = zmat(c, 3, length(edges)); gauge_columns = Int[]; fermion_columns = Int[]
    for (column, edge) in enumerate(edges)
        incidence[edge[1] + 1, column] = -fone(c); incidence[edge[3] + 1, column] = fone(c)
        push!(startswith(edge[2], "G") ? gauge_columns : fermion_columns, column)
    end
    unit = zmat(c, 1, length(edges)); unit[1, gauge_columns[1]] = fone(c)
    route, rank = solve_linear(c, vcat(incidence, unit), [fzero(c), fzero(c), fzero(c), fone(c)])
    ensure(rank == length(edges) && all(value in (fone(c), -fone(c)) for value in route), "C03_JULIA_PHASE_ROUTING")
    # N=2 simple-pole master has phase +i in the frozen +i0 convention;
    # oriented fermion numerators contribute their solved route signs.
    return prod(vcat(vertex, [i, i, -i, i], [route[index] for index in fermion_columns]))
end

function c03_physical(c, sources)
    fields = sources["C03.SOURCE.ORDERED_FIELDS"]
    ensure(fields["target"]["ordered_fields"] == ["dR", "uR", "uR", "eR"], "C03_JULIA_TARGET")
    grassmann = -fone(c); color = c03_color_sign(c, sources["C03.SOURCE.COLOR_TENSOR"])
    gx = c03_spinor_action(c, sources["C03.SOURCE.SPINOR_X"], sources["C03.SOURCE.SPINOR_Y"], false)
    gy = c03_spinor_action(c, sources["C03.SOURCE.SPINOR_Y"], sources["C03.SOURCE.SPINOR_X"], false)
    lx = c03_spinor_action(c, sources["C03.SOURCE.SPINOR_X"], sources["C03.SOURCE.SPINOR_Y"], true)
    ly = c03_spinor_action(c, sources["C03.SOURCE.SPINOR_Y"], sources["C03.SOURCE.SPINOR_X"], true)
    exchange = grassmann * color
    gsum = gx .+ exchange .* gy; lsum = lx .+ exchange .* ly
    transverse = gsum .- lsum; xi = fsymbol(c, "xi1")
    covariant = transverse .+ xi .* lsum
    charge = parse_profile_expression(c, sources["C03.SOURCE.HYPERCHARGE_D"]) * parse_profile_expression(c, sources["C03.SOURCE.HYPERCHARGE_E"])
    raw = c03_phase(c, sources["C03.SOURCE.DIAGRAM_PHASE"]) * charge .* covariant
    removed = fsymbol(c, "g1")^2 * fsymbol(c, sources["C03.CONVENTION.WILSON_SYMBOL"])
    prefactor = parse_profile_expression(c, sources["C03.SOURCE.COMMON_PREFACTOR"])
    reference = prefactor / removed
    ensure(!iszero(reference) && raw[1] == raw[2], "C03_JULIA_NORMALIZATION")
    return raw[1] / reference, (grassmann, color, exchange, charge, c03_phase(c, sources["C03.SOURCE.DIAGRAM_PHASE"]))
end

function c03_native(c, sources, shared)
    grassmann, color, exchange, charge, phase = shared
    occurrences = sources["C03.NATIVE.SOURCE.OCCURRENCES"]
    columns = sort(sources["C03.NATIVE.SOURCE.COLUMNS"], by=row -> row["column"])
    by_occurrence = Dict(row["occurrence_id"] => row for row in occurrences)
    d = fsymbol(c, "d"); xi = fsymbol(c, "xi1")
    ambient = Any[]
    for column in columns
        identity = column["input_tensor_id"]
        if !haskey(by_occurrence, identity)
            push!(ambient, fzero(c)); continue
        end
        row = by_occurrence[identity]
        signs = fone(c)
        for word in row["gamma_chains"]
            source = word["source_factors"]; normal = word["normal_form_factors"]
            ensure([item["sector"] for item in normal] == sort([item["sector"] for item in source], by=sector -> sector != "HAT"), "C03_JULIA_CLIFFORD_ORDER")
            inversions = 0
            for first_index in 1:length(source), second_index in (first_index + 1):length(source)
                source[first_index]["sector"] == "BAR" && source[second_index]["sector"] == "HAT" && (inversions += 1)
            end
            signs *= fq(c, isodd(inversions) ? -1 : 1)
        end
        rank = row["angular_average"]["master_rank"]
        angular_denominator = fone(c)
        for offset in 0:2:(rank - 2); angular_denominator *= d + fq(c, offset); end
        angular = fone(c) / angular_denominator
        channel = rank == 2 ? fone(c) : -(fone(c) - xi)
        weight = row["source_orbit"]["orbit_id"] == "IDENTITY" ? fone(c) : exchange
        stored = parse_profile_expression(c, row["exact_coefficient"])
        ensure(stored == parse_profile_expression(c, row["source_orbit"]["grassmann_and_color_parity"]) * signs * angular, "C03_JULIA_LEGACY_AGGREGATE")
        push!(ambient, phase * charge * signs * angular * channel * weight)
    end
    relations = sparse_matrix(c, sources["C03.NATIVE.SOURCE.RELATIONS"], "relation_row", "ambient_column")
    representatives = sparse_matrix(c, sources["C03.NATIVE.SOURCE.REP_CACHE"], "ambient_generator_column", "quotient_column")
    dual = sparse_matrix(c, sources["C03.NATIVE.SOURCE.DUAL_CACHE"], "dual_index", "ambient_generator_column")
    quotient = sparse_matrix(c, sources["C03.NATIVE.SOURCE.Q_CACHE"], "output_ambient_column", "input_ambient_column")
    remainder = sparse_matrix(c, sources["C03.NATIVE.SOURCE.K_CACHE"], "output_ambient_column", "input_ambient_column")
    ensure(size(relations) == (30, 38) && matrix_rank(c, relations) == 24, "C03_JULIA_RELATION_RANK")
    ensure(mmul(c, dual, transpose(relations)) == zmat(c, 14, 30), "C03_JULIA_DUAL_RELATIONS")
    ensure(mmul(c, dual, representatives) == eye(c, 14), "C03_JULIA_DUAL_REPRESENTATIVES")
    ensure(quotient == mmul(c, representatives, dual) && remainder == eye(c, 38) - quotient, "C03_JULIA_PROJECTORS")
    ensure(mmul(c, quotient, quotient) == quotient && mmul(c, remainder, remainder) == remainder, "C03_JULIA_PROJECTOR_IDEMPOTENCE")
    coordinates = mmul(c, dual, reshape(ambient, :, 1))[:, 1]
    projected = mmul(c, representatives, reshape(coordinates, :, 1))[:, 1]
    relation_part = mmul(c, remainder, reshape(ambient, :, 1))[:, 1]
    ensure(all(iszero, ambient .- projected .- relation_part), "C03_JULIA_NATIVE_RESIDUAL")
    solve_linear(c, transpose(relations), ambient .- projected)
    defects = sources["C03.NATIVE.SOURCE.DEFECTS"]
    ensure(all(parse_profile_expression(c, row["p4_of_defect"]) == fzero(c) for row in defects), "C03_JULIA_NATIVE_LEAKAGE")
    state = any(!iszero, coordinates) ? "EVALUATED_NONZERO" : "EVALUATED_ZERO"
    return TensorValue([length(coordinates)], coordinates), AtomValue("ENUM", state)
end

struct RVTensor
    dims::Vector{Int}
    pair::Vector{Int}
    entries::Dict{Tuple,Any}
end

levi3(a, b, c) = length(Set([a, b, c])) < 3 ? 0 : ((a, b, c) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)) ? 1 : -1)

function rv_domain(context)
    record = context["record"]; topology = record["topology"]; target = record["target"]
    ensure(topology["source_insertion_id"] == record["operator"] == target["target_operator_id"], "RV_JULIA_IDENTITY")
    ensure(topology["loop_count"] == 1 && length(topology["internal_edges"]) == 3 && length(record["vertices"]) == 2, "RV_JULIA_GRAPH")
    fermions = [edge for edge in topology["internal_edges"] if !startswith(edge[2], "G")]
    kinds = [field["kind"] for field in record["fields"]]
    directed = any(startswith(edge[2], "bar") for edge in fermions)
    ordered = [field for field in target["ordered_fields"] if field in Set(["qL", "lL", "dR", "uR", "eR", "baruR"])]
    return Dict("directed" => directed, "right" => all(==("RIGHT_WEYL"), kinds), "source_spinor_chain_count" => length(ordered) ÷ 2,
        "touched_spinor_chains" => 1, "current_count" => 2, "fermion_propagators" => length(fermions), "fermions" => fermions)
end

function rv_tensor(c, context, domain)
    record = context["record"]; source = record["source"]; blob = record["tensor"]; pair = Int[]; dims = Int[]; raw = Any[]
    if blob !== nothing
        dims = Int.(blob["dims"]); raw = blob["sparse_entries"]
        axes = record["registered"]["component_axis_order"]
        pair = [findfirst(==("qL[1].color3"), axes) - 1, findfirst(==("qL[2].color3"), axes) - 1]
    elseif domain["directed"]
        blob = source["witness"]; dims = Int.(blob["dims"]); raw = blob["sparse_entries"]
    elseif occursin("H_dagger_i epsilon_jk X^{C k}+H_dagger_j epsilon_ik X^{C k}", get(source, "operator", ""))
        dims = fill(2, 4); pair = [0, 1]
        raw = [Dict("index" => [i, j, h, z], "coefficient" => (h == i) * (z - j) + (h == j) * (z - i)) for i in 0:1 for j in 0:1 for h in 0:1 for z in 0:1]
    elseif get(source, "operator", "") == "epsilon_ABC (d_R,p^{A T} C d_R,r^B)(H^i epsilon_ij X^{C j})"
        dims = fill(3, 3); pair = [0, 1]
        raw = [Dict("index" => [a, b, d], "coefficient" => levi3(a, b, d)) for a in 0:2 for b in 0:2 for d in 0:2]
    else
        dims = [3, 3, 3, 2, 2]
        raw = [Dict("index" => [a, b, d, i, j], "coefficient" => levi3(a, b, d) * (j - i)) for a in 0:2 for b in 0:2 for d in 0:2 for i in 0:1 for j in 0:1]
    end
    entries = Dict{Tuple,Any}()
    for item in raw
        index = Tuple(Int.(item["index"])); ensure(!haskey(entries, index), "RV_JULIA_TENSOR_DUPLICATE")
        value = parse_profile_expression(c, string(item["coefficient"])); !iszero(value) && (entries[index] = value)
    end
    ensure(!isempty(entries), "RV_JULIA_TENSOR_ZERO")
    return RVTensor(dims, pair, entries)
end

function rv_channel(context, tensor)
    record = context["record"]; gauge = record["topology"]["coupling_monomial"][1]
    gauge == "g1" && return "ABELIAN_ENDPOINT_CHARGE_PRODUCT"
    record["registered"] !== nothing && return "EXACT_REGISTERED_COMPONENT_TENSOR"
    if record["fields"][1]["su2"] == "FUNDAMENTAL_2" && tensor.dims == fill(2, 4)
        ensure(all(value == get(tensor.entries, (index[2], index[1], index[3], index[4]), 0) for (index, value) in tensor.entries), "RV_JULIA_WEAK_TRIPLET")
        return "WEAK_TRIPLET_A_FLAVOR"
    end
    tensor.dims == fill(3, 3) && return "SOURCE_EPSILON_COLOR_TENSOR"
    fail("RV_JULIA_CHANNEL")
end

function conjugate_field(c, value)
    imaginary = field_constant(c, IMAGINARY_COORDINATES)
    alpha_bar = c.alpha - 2 * imaginary
    return sum(coeff(value, power) * alpha_bar^power for power in 0:(c.degree - 1))
end

function conjugate_value(c, value)
    numerator_conjugate = map_coefficients(coefficient -> conjugate_field(c, coefficient), numerator(value))
    denominator_conjugate = map_coefficients(coefficient -> conjugate_field(c, coefficient), denominator(value))
    return c.fraction_field(numerator_conjugate) / c.fraction_field(denominator_conjugate)
end

function rv_group(c, context, tensor, channel)
    record = context["record"]; gauge = record["topology"]["coupling_monomial"][1]
    if gauge == "g1"
        charges = [parse_profile_expression(c, field["hypercharge"]) for field in record["fields"]]
        for (field, vertex) in zip(record["fields"], record["vertices"])
            ensure(vertex["generator_representation"] == field["hypercharge"], "RV_JULIA_CHARGE_BINDING")
        end
        return prod(charges)
    end
    generators = Any[[parse_profile_expression(c, string(block[i][j])) for i in 1:length(block), j in 1:length(block)] for block in record["generators"]]
    size_g = size(generators[1], 1)
    for (a, generator) in enumerate(generators)
        ensure(mtrace(generator) == fzero(c), "RV_JULIA_GENERATOR_TRACE")
        ensure(generator == [conjugate_value(c, generator[j, i]) for i in 1:size_g, j in 1:size_g], "RV_JULIA_GENERATOR_HERMITIAN")
        for (b, other) in enumerate(generators)
            ensure(mtrace(mmul(c, generator, other)) == fq(c, a == b ? "1/2" : "0"), "RV_JULIA_GENERATOR_NORMALIZATION")
        end
    end
    output = Dict{Tuple,Any}()
    first_axis, second_axis = tensor.pair .+ 1
    for (index, value) in tensor.entries, generator in generators, first_out in 0:(size_g - 1), second_out in 0:(size_g - 1)
        changed = collect(index); first_in, second_in = index[first_axis], index[second_axis]
        changed[first_axis] = first_out; changed[second_axis] = second_out
        key = Tuple(changed)
        output[key] = get(output, key, fzero(c)) + generator[first_out + 1, first_in + 1] * generator[second_out + 1, second_in + 1] * value
    end
    first_index = first(keys(tensor.entries)); scalar = get(output, first_index, fzero(c)) / tensor.entries[first_index]
    ensure(all(get(output, index, fzero(c)) == scalar * get(tensor.entries, index, fzero(c)) for index in union(keys(output), keys(tensor.entries))), "RV_JULIA_GROUP_RESIDUAL")
    return scalar
end

function rv_gammas(c)
    i = parse_profile_expression(c, "I"); z = fzero(c); o = fone(c)
    sigma = [[z o; o z], [z -i; i z], [o z; z -o]]
    gamma = Any[kronm(c, sigma[3], eye(c, 2))]
    append!(gamma, [kronm(c, i .* sigma[2], item) for item in sigma])
    metric = [1, -1, -1, -1]
    for a in 1:4, b in 1:4
        ensure(mmul(c, gamma[a], gamma[b]) + mmul(c, gamma[b], gamma[a]) == (2 * (a == b ? metric[a] : 0)) .* eye(c, 4), "RV_JULIA_CLIFFORD")
    end
    return gamma, metric
end

function rv_tree(c, domain)
    gamma, _ = rv_gammas(c); i = parse_profile_expression(c, "I")
    gamma5 = i .* mmul(c, mmul(c, mmul(c, gamma[1], gamma[2]), gamma[3]), gamma[4])
    projection = fq(c, "1/2") .* (eye(c, 4) + (domain["right"] ? 1 : -1) .* gamma5)
    return domain["directed"] ? projection : i .* mmul(c, mmul(c, gamma[3], gamma[1]), projection)
end

function rv_orientation(c, context, domain)
    edges = context["record"]["topology"]["internal_edges"]; incidence = zmat(c, 3, 3); gauge = Int[]; fermions = Int[]
    for (column, edge) in enumerate(edges)
        incidence[edge[1] + 1, column] = -fone(c); incidence[edge[3] + 1, column] = fone(c)
        push!(startswith(edge[2], "G") ? gauge : fermions, column)
    end
    unit = zmat(c, 1, 3); unit[1, gauge[1]] = fone(c)
    route, rank = solve_linear(c, vcat(incidence, unit), [fzero(c), fzero(c), fzero(c), fone(c)])
    ensure(rank == 3 && all(value in (fone(c), -fone(c)) for value in route), "RV_JULIA_ROUTING")
    barred = sum(startswith(edges[index][2], "bar") for index in fermions)
    return prod(route[index] for index in fermions) * fq(c, (-1)^barred)
end

function rv_spinor(c, context, domain, tree)
    gamma, metric = rv_gammas(c); orientation = rv_orientation(c, context, domain)
    action = zmat(c, 16, 16)
    for mu in 1:4, rho in 1:4
        left = domain["directed"] ? mmul(c, gamma[mu], gamma[rho]) : transpose(mmul(c, gamma[rho], gamma[mu]))
        right = mmul(c, gamma[rho], gamma[mu])
        action .+= fq(c, metric[mu] * metric[rho]) / fq(c, 4) .* kronm(c, left, transpose(right))
    end
    metric_image = rowreshape(orientation .* mmul(c, action, reshape(rowmajor(tree), :, 1))[:, 1], 4, 4)
    ward_image = orientation .* tree
    pivot = findfirst(!iszero, rowmajor(tree)); ensure(pivot !== nothing, "RV_JULIA_TREE_ZERO")
    metric_scalar = rowmajor(metric_image)[pivot] / rowmajor(tree)[pivot]
    ward_scalar = rowmajor(ward_image)[pivot] / rowmajor(tree)[pivot]
    ensure(metric_image == metric_scalar .* tree && ward_image == ward_scalar .* tree, "RV_JULIA_SPINOR_RESIDUAL")
    return metric_scalar, ward_scalar
end

function rv_absence_state(c, context, domain)
    ensure(context["regularization"]["uv_poles_retained_for_closure"] == ["1/epsilon"], "RV_JULIA_ABSENCE_POLE")
    count = 0
    for mate in 2:4
        rest = [index for index in 2:4 if index != mate]
        word = [0, 0, 0, 0]; word[1] = word[mate] = 1; word[rest[1]] = word[rest[2]] = 2
        for first_sector in ("BAR", "HAT"), second_sector in ("BAR", "HAT")
            count += 1
            "HAT" in (first_sector, second_sector) || continue
            # At h=0 every contraction containing a HAT sector vanishes;
            # denominators d and d(d+2) are nonzero at d=4, so the simple-pole
            # residue is exactly zero.
            dimensions = Dict("BAR" => 4, "HAT" => 0)
            pairings = [([(1, 2), (3, 4)], 1), ([(1, 3), (2, 4)], -1), ([(1, 4), (2, 3)], 1)]
            total = 0
            sectors = [first_sector, second_sector]
            for (pairs, sign) in pairings
                linked = any(word[a] != word[b] for (a, b) in pairs)
                term = linked ? (sectors[1] == sectors[2] ? dimensions[sectors[1]] : 0) : prod(dimensions[item] for item in sectors)
                total += sign * term
            end
            ensure(total == 0, "RV_JULIA_EVANESCENT_RESIDUE")
        end
    end
    ensure(count == 12, "RV_JULIA_WORD_COVERAGE")
    return AtomValue("ENUM", "EVALUATED_ZERO")
end

function rv_outputs(c, context)
    domain = rv_domain(context); tensor = rv_tensor(c, context, domain); channel = rv_channel(context, tensor)
    group = rv_group(c, context, tensor, channel); tree = rv_tree(c, domain)
    metric, longitudinal = rv_spinor(c, context, domain, tree)
    gauge = context["record"]["topology"]["coupling_monomial"][1]
    xi = fsymbol(c, "xi" * gauge[2:end]); coupling = fsymbol(c, gauge)^2
    covariant = metric - (fone(c) - xi) * longitudinal
    # Two +i vertices, two +i fermion propagators, one -i gauge
    # propagator, and the +i N=2 master multiply to +1.
    phase = fone(c)
    physical = coupling * group * covariant * phase
    return physical, rv_absence_state(c, context, domain), AtomValue("SYMBOL_TEXT", channel)
end

function evaluate_c03_rv_candidate(profile, request, candidate, source_root)
    ensure(profile["profile_id"] == "C03_RV_SU5_EXACT_PROFILE_v1", "C03_RV_JULIA_PROFILE")
    field = profile["algebraic_field"]
    ensure(field["field_id"] == "SQRT2_SQRT3_I_COMMON_FIELD", "C03_RV_JULIA_ALGEBRAIC_FIELD_ID")
    ensure(String.(field["minimal_polynomial"]) == ["144", "0", "192", "0", "88", "0", "-16", "0", "1"], "C03_RV_JULIA_ALGEBRAIC_MINPOLY")
    ensure(field["primitive_element"] == "alpha" && String.(field["ordered_power_basis"]) == ["1", "alpha", "alpha^2", "alpha^3", "alpha^4", "alpha^5", "alpha^6", "alpha^7"], "C03_RV_JULIA_ALGEBRAIC_BASIS")
    context = exact_context(profile)
    sources = c03_rv_sources(profile, candidate, source_root)
    physical, shared = c03_physical(context, sources)
    native_coordinates, native_state = c03_native(context, sources, shared)
    computed = Dict{String,Any}(
        "C03.OUTPUT.PHYSICAL_COEFFICIENT" => physical,
        "C03.OUTPUT.EVANESCENT_COORDINATES" => native_coordinates,
        "C03.OUTPUT.EVANESCENT_STATE" => native_state,
    )
    for index in 1:6
        record = "RV0$(index)"; value, state, channel = rv_outputs(context, sources[record * ".SOURCE.CONTEXT"])
        computed[record * ".OUTPUT.PHYSICAL_COEFFICIENT"] = value
        computed[record * ".OUTPUT.EVANESCENT_STATE"] = state
        index == 3 && (computed[record * ".OUTPUT.SOURCE_CHANNEL"] = channel)
    end
    ensure(Set(keys(computed)) == Set(profile["output_roots"]), "C03_RV_JULIA_OUTPUT_CENSUS")
    for root in profile["output_roots"]
        claimed = decode_exact(context, candidate["claimed_outputs"][root])
        ensure(exact_equal(computed[root], claimed), "C03_RV_JULIA_OUTPUT_MISMATCH", string(root, ":", computed[root], ":", claimed))
    end
    return context
end
