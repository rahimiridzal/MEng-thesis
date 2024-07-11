function tep(areas,generators,vres,nodes,kperiods,fullcac,fullcdc,slacks;
    years = 10,
    mip_gap = 0.05,
    CAP_max = 6000,
    ac_fixed_cost = 278.2e6,
    dc_fixed_cost = 1376.3e6,
    ac_var_cost = 3091.29,
    dc_var_cost = 2245.11,
    d = 0.05,
    load_rate = 0.02,
    gen_rate = 0.01,
    vre_rate = 0.05,
    bigM = 10000,
    Sbase = 100,
    beta = 0.67,
    reserve_exchange = false,
    budget_based = false,
    )
    model = Model()
    set_optimizer(model,HiGHS.Optimizer)
    set_silent(model)
    set_optimizer_attribute(model,"mip_rel_gap",mip_gap)

    # convenience
    AREAS = copy(areas)
    GENS = copy(generators)
    VRES = copy(vres)
    NODES = copy(nodes)
    PER = copy(kperiods)
    HVACS = copy(fullcac)
    HVDCS = copy(fullcdc)

    # sets
    A, G, V, N = AREAS.id, GENS.id, VRES.id, NODES.id
    P, CAC, CDC = PER.id, HVACS.id, HVDCS.id
    Y = 1:years

    # variables
    @variables(model, begin
        en[G,P,Y] >= 0
        vre[V,P,Y] >= 0
        ru[G,P,Y] >= 0
        rd[G,P,Y] >= 0
        ens[N,P,Y] >= 0
        fac[CAC,P,Y]
        fdc[CDC,P,Y]
        alpha_ac[CAC,Y], Bin
        alpha_dc[CDC,Y], Bin
        0 <= cap_ac[CAC,Y] <= CAP_max
        0 <= cap_dc[CDC,Y] <= CAP_max
        theta[N,P,Y]
    end)

    # set slack nodes
    for slack in slacks
        for p in P
            for y in Y
                fix(theta[slack,p,y],0,force=true)
            end
        end
    end

    # costs
    @expression(model, TCostEn[y in Y], 
        sum(PER[p,:w] *
            (sum(GENS[g,:encost]*en[g,p,y] for g in G) 
            + sum(VRES[v,:encost]*vre[v,p,y] for v in V)) 
            for p in P)
    )
    @expression(model, TCostAs[y in Y],
        sum(PER[p,:w] * 
            sum(GENS[g,:rucost]*ru[g,p,y] + GENS[g,:rdcost]*ru[g,p,y] for g in G)
            for p in P)
    )
    @expression(model, TCostEns[y in Y],
        sum(PER[p,:w] *
            sum(AREAS[a,:voll]*ens[i,p,y] for i in NODES[NODES.area.==a,:id])
            for p in P for a in A)
    )
    @expression(model, TCostIntraInv[a in A, y in Y],
        sum(ac_fixed_cost*alpha_ac[l,y] + ac_var_cost*cap_ac[l,y] 
            for l in HVACS[(HVACS.f_area.==a) .& (HVACS.t_area.==a),:id])
        +
        sum(dc_fixed_cost*alpha_dc[l,y] + dc_var_cost*cap_dc[l,y] 
            for l in HVDCS[(HVDCS.f_area.==a) .& (HVDCS.t_area.==a),:id])
    )
    @expression(model, TCostCrossInv[y in Y],
        sum(dc_fixed_cost*alpha_dc[l,y] + dc_var_cost*cap_dc[l,y] 
            for l in HVDCS[HVDCS.f_area .!= HVDCS.t_area,:id])
    )
    @expression(model, TCostInv[y in Y], 
        TCostCrossInv[y] + sum(TCostIntraInv[a,y] for a in A)
    )
    if budget_based
        @constraint(model, cBudget[a in A, y in Y], 
            sum(TCostIntraInv[a,zeta] + areas[a,:commitment] * TCostCrossInv[zeta] for zeta in minimum(Y):y) <= y * areas[a,:budget]
        )
        @objective(model, Min, sum( (1/((1+d)^(y-1))) * 
            (TCostEn[y] + TCostAs[y] + TCostEns[y]) for y in Y)    
    )
    else
        # objective
        @objective(model, Min, sum( (1/((1+d)^(y-1))) * 
            (TCostEn[y] + TCostAs[y] + TCostEns[y] + TCostInv[y]) for y in Y)    
        )
    end

    # constraints
    @constraint(model, cKCL[i in N,p in P,y in Y],
        sum(en[g,p,y] for g in GENS[GENS.node.==i,:id]) +
        sum(vre[v,p,y] for v in  VRES[VRES.node.==i,:id]) +
        sum(ens[i,p,y]) +
        sum(fac[l,p,y] for l in HVACS[HVACS.t_node.==i,:id]) -
        sum(fac[l,p,y] for l in HVACS[HVACS.f_node.==i,:id]) +
        sum(fdc[l,p,y] for l in HVDCS[HVDCS.t_node.==i,:id]) -
        sum(fdc[l,p,y] for l in HVDCS[HVDCS.f_node.==i,:id]) ==
        PER[p,"load"*NODES[i,:name]] * (1 + load_rate)^(y-1)
    )
    @constraint(model, cKVL1[l in CAC,p in P,y in Y],
        fac[l,p,y] - (Sbase / HVACS[l,:x] * 
        (theta[HVACS[l,:f_node],p,y] - theta[HVACS[l,:t_node],p,y])) <= 
        bigM * (1 - sum(alpha_ac[l,zeta] for zeta in minimum(Y):y))
    )
    @constraint(model, cKVL2[l in CAC,p in P,y in Y],
        fac[l,p,y] - (Sbase / HVACS[l,:x] * 
        (theta[HVACS[l,:f_node],p,y] - theta[HVACS[l,:t_node],p,y])) >= 
        -(bigM * (1 - sum(alpha_ac[l,zeta] for zeta in minimum(Y):y)))
    )
    @constraint(model, cACUpper[l in CAC, p in P, y in Y],
        fac[l,p,y] <= sum(alpha_ac[l,zeta] for zeta in minimum(Y):y) * CAP_max
    )
    @constraint(model, cACLower[l in CAC, p in P, y in Y],
        fac[l,p,y] >= -(sum(alpha_ac[l,zeta] for zeta in minimum(Y):y) * CAP_max)
    )
    @constraint(model, cCapACLimit[l in CAC, p in P, y in Y],
        cap_ac[l,y] <= alpha_ac[l,y] * CAP_max
    )
    @constraint(model, cACLimitMax[l in CAC, p in P, y in Y],
        fac[l,p,y] <= sum(cap_ac[l,zeta] for zeta in minimum(Y):y) + 
        CAP_max * (1 - sum(alpha_ac[l,zeta] for zeta in minimum(Y):y))
    )
    @constraint(model, cACLimitMin[l in CAC, p in P, y in Y],
        fac[l,p,y] >= -(sum(cap_ac[l,zeta] for zeta in minimum(Y):y) + 
        CAP_max * (1 - sum(alpha_ac[l,zeta] for zeta in minimum(Y):y)))
    )
    @constraint(model, cDCUpper[l in CDC, p in P, y in Y],
        fdc[l,p,y] <= sum(alpha_dc[l,zeta] for zeta in minimum(Y):y) * CAP_max
    )
    @constraint(model, cDCLower[l in CDC, p in P, y in Y],
        fdc[l,p,y] >= -(sum(alpha_dc[l,zeta] for zeta in minimum(Y):y) * CAP_max)
    )
    @constraint(model, cCapDCLimit[l in CDC, p in P, y in Y],
        cap_dc[l,y] <= alpha_dc[l,y] * CAP_max
    )
    @constraint(model, cDCLimitMax[l in CDC, p in P, y in Y],
        fdc[l,p,y] <= sum(cap_dc[l,zeta] for zeta in minimum(Y):y) + 
        CAP_max * (1 - sum(alpha_dc[l,zeta] for zeta in minimum(Y):y))
    )
    @constraint(model, cDCLimitMin[l in CDC, p in P, y in Y],
        fdc[l,p,y] >= -(sum(cap_dc[l,zeta] for zeta in minimum(Y):y) + 
        CAP_max * (1 - sum(alpha_dc[l,zeta] for zeta in minimum(Y):y)))
    )
    @constraint(model, cGenMax[g in G, p in P, y in Y],
        en[g,p,y] + ru[g,p,y] <= GENS[g,:pmax] * GENS[g,:pu_max] * (1 + gen_rate)^(y-1)
    )
    @constraint(model, cGenMin[g in G, p in P, y in Y],
        en[g,p,y] - rd[g,p,y] >= GENS[g,:pmax] * GENS[g,:pu_min]
    )
    @constraint(model, cVreMax[v in V, p in P, y in Y],
        vre[v,p,y] <= 
        PER[p,VRES[v,:type]*NODES[VRES[v,:node],:name]] * VRES[v,:pmax] * (1+vre_rate)^(y-1)
    )
    @constraint(model, cAlphaAc[l in CAC], sum(alpha_ac[l,y] for y in Y) <= 1)
    @constraint(model, cAlphaDc[l in CDC], sum(alpha_dc[l,y] for y in Y) <= 1)

    if reserve_exchange
        @constraint(model, cReserveReqUp[a in A, p in P, y in Y],
            sum(ru[g,p,y] for g in GENS[GENS.area.==a,:id]) >= beta * AREAS[a,:reqru]
        )
        @constraint(model, cReserveReqDown[a in A, p in P, y in Y],
            sum(rd[g,p,y] for g in GENS[GENS.area.==a,:id]) >= beta * AREAS[a,:reqrd]
        )
        @constraint(model, cOverallUp[p in P, y in Y],
            sum(ru[g,p,y] for g in G) >= sum(AREAS[a,:reqru] for a in A)
        )
        @constraint(model, cOverallDown[p in P, y in Y],
            sum(rd[g,p,y] for g in G) >= sum(AREAS[a,:reqrd] for a in A)
        )
        @constraint(model, cNetUp[a in A, p in P, y in Y],
            sum(ru[g,p,y] + en[g,p,y] for g in GENS[GENS.area.==a,:id]) +
            sum(vre[v,p,y] for v in VRES[VRES.area.==a,:id]) -
            AREAS[a,:reqru] -
            sum(ens[i,p,y] + PER[p,"load"*NODES[i,:name]]*((1+load_rate)^(y-1)) 
            for i in NODES[NODES.area.==a,:id]) <=
            sum(sum(cap_dc[l,zeta] for l in HVDCS[(HVDCS.f_area.==a) .!= (HVDCS.t_area.==a),:id]) for zeta in minimum(Y):y)
        )
        @constraint(model, cNetDown[a in A, p in P, y in Y],
            sum(rd[g,p,y] - en[g,p,y] for g in GENS[GENS.area.==a,:id]) -
            sum(vre[v,p,y] for v in VRES[VRES.area.==a,:id]) - 
            AREAS[a,:reqrd] +
            sum(ens[i,p,y] + PER[p,"load"*NODES[i,:name]]*((1+load_rate)^(y-1))  
            for i in NODES[NODES.area.==a,:id]) <=
            sum(sum(cap_dc[l,zeta] for l in HVDCS[(HVDCS.f_area.==a) .!= (HVDCS.t_area.==a),:id]) for zeta in minimum(Y):y)
        )
    else
        @constraint(model, cReserveReqUp[a in A, p in P, y in Y],
            sum(ru[g,p,y] for g in GENS[GENS.area.==a,:id]) >= AREAS[a,:reqru]
        )
        @constraint(model, cReserveReqDown[a in A, p in P, y in Y],
            sum(rd[g,p,y] for g in GENS[GENS.area.==a,:id]) >= AREAS[a,:reqrd]
        )
    end
    optimize!(model)

    return(
        Obj = objective_value(model),
        TCostEn = value.(TCostEn).data,
        TCostAs = value.(TCostAs).data,
        TCostEns = value.(TCostEns).data,
        TCostIntraInv = value.(TCostIntraInv).data,
        TCostCrossInv = value.(TCostCrossInv).data,
        TCostInv = value.(TCostInv).data,
        en = value.(en).data,
        vre = value.(vre).data,
        ru = value.(ru).data,
        rd = value.(rd).data,
        ens = value.(ens).data,
        fac = value.(fac).data,
        fdc = value.(fdc).data,
        alpha_ac = value.(alpha_ac).data,
        alpha_dc = value.(alpha_dc).data,
        cap_ac = value.(cap_ac).data, 
        cap_dc = value.(cap_dc).data,
        theta = value.(theta).data,
    )
end