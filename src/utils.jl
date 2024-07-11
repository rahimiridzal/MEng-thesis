"""Function to get k representative periods"""
function getKRepresentativePeriods(
    ts_dicts::Dict,
    nodes;k=20,norm="minmax",seed=910
)
    # dictionary to concatenated array
    ts_data = hcat(Array.(collect(values(ts_dicts)))...)
    ts_df = DataFrame()
    
    # zscore or minmax normalisation
    if norm=="zscore"
        ts_data_norm = (ts_data .- mean(ts_data,dims=1)) ./ std(ts_data,dims=1)
    elseif norm=="minmax"
        ts_data_norm = (ts_data .- minimum(ts_data,dims=1)) ./ 
            (maximum(ts_data,dims=1) .- minimum(ts_data,dims=1))
    else
        ts_data_norm = ts_data
    end
    ts_data_norm[isinf.(ts_data_norm)] .= 0
    ts_data_norm[isnan.(ts_data_norm)] .= 0

    # seed for reproducibility
    Random.seed!(seed)
    clusters = kmeans(ts_data_norm',k)
    
    # prepare column names
    colnames = []
    for key in keys(ts_dicts)
        for node in nodes.name
            push!(colnames,"$key$node")
        end
    end

    # denormalise and get DataFrame
    if norm=="zscore"
        ts_df = DataFrame(
            Array(clusters.centers') .* std(ts_data,dims=1) .+ 
            mean(ts_data,dims=1),colnames)
        ts_df[!,:w] = counts(clusters)
    elseif norm=="minmax"
        ts_df = DataFrame(
            Array(clusters.centers') .* (maximum(ts_data,dims=1) .- minimum(ts_data,dims=1)) .+ 
            minimum(ts_data,dims=1),colnames)
        ts_df[!,:w] = counts(clusters)
    else
        ts_df = Array(clusters.centers')
    end
    ts_df.id = 1:nrow(ts_df)
    ts_df = select(ts_df,:id,:)
    ts_df
end   

"""Function to get steps and step hours for duration curve"""
function getDurationCurve(
    ts_df::DataFrame;
    node="Norway",type="load"
)
    ts_node = sort(select(ts_df,r""*type*"")[:,type*node],rev=true)
    steps = []
    step_hours = []
    cumulative_hours = 0
    for i in eachindex(ts_node)
        push!(steps, ts_node[i])
        cumulative_hours += sort(ts_df,type*node,rev=true)[i,:w]
        push!(step_hours, cumulative_hours)
    end
    step_hours, steps
end

"""Function to get haversine distance between two pair of geo-coordinates"""
function getHaversineDistance(
    latitude_1, longitude_1, latitude_2, longitude_2
)
    R = 6371e3
    phi1 = latitude_1 * pi/180
    phi2 = latitude_2 * pi/180
    deltaphi = (latitude_2 - latitude_1) * pi/180
    deltalambda = (longitude_2 - longitude_1) * pi/180
    a = sin(deltaphi/2)^2 + cos(phi1) * cos(phi2) * sin(deltalambda/2)^2
    c = 2 * atan(sqrt(a), sqrt(1-a))
    d = R * c
    return d * 1e-3
end

"""Function to get full candidate lines"""
function getFullCandidateLines(
    nodes::DataFrame,elines::DataFrame;
    ignore_area=true,hvdc=false,kv_nom=400,greenfield=true
)
    clines = Vector()
    if ignore_area
        clines = collect(Iterators.flatten(combinations(nodes.id,2)))
    else
        for a in unique(nodes.area)
            append!(clines, collect(Iterators.flatten(combinations(nodes[nodes.area.==a,:id],2))))
        end
    end
    clines = Array(reshape(clines,(2,:))')
    clines = DataFrame(clines,["f_node","t_node"])
    clines.id = 1:size(clines)[1]
    clines = select(clines, :id, :f_node, :t_node)
    clines.f_area = nodes[clines.f_node,:area]
    clines.t_area = nodes[clines.t_node,:area]
    clines[!,:length] =  map(getHaversineDistance, 
        nodes[clines.f_node,:latitude], nodes[clines.f_node,:longitude], 
        nodes[clines.t_node,:latitude], nodes[clines.t_node,:longitude])
    if hvdc
        clines[!,:r] = clines.length .* 0.0378 ./ ((kv_nom*1e3)^2/100e6)
    else
        clines[!,:x] = clines.length .* 0.327 ./ ((kv_nom*1e3)^2/100e6)
    end
    if greenfield == false
        clines[!,:existing_capacity] .= 0
        for (f,t) in zip(elines.f_node,elines.t_node)
            if isempty(clines[(clines.f_node.==f).&(clines.t_node.==t),:])
                if isempty(clines[(clines.f_node.==t).&(clines.t_node.==f),:])
                else
                    clines[(clines.f_node.==t).&(clines.t_node.==f),:existing_capacity] .= 
                        elines[(elines.f_node.==f).&(elines.t_node.==t),:existing_capacity][1]
                end
            else
                clines[(clines.f_node.==f).&(clines.t_node.==t),:existing_capacity] .=
                    elines[(elines.f_node.==f).&(elines.t_node.==t),:existing_capacity][1]
            end
        end
    else
    end
    clines
end