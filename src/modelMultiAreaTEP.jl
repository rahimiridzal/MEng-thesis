function modelMultiAreaTEP(
    nodes::DataFrame, generators::DataFrame, vres::DataFrame, 
    schvacs::DataFrame, schvdcs::DataFrame, periods::DataFrame,areas::DataFrame,
    slacks::Vector;
    silent=false,
    costacf=278.2e6, costacv=3091.29,
    costdcf=1376.3e6, costdcv=2245.11, 
    years=10, Sbase=100, bigM=10000, epsilon=0.05, maxcap=6000,
    d=0.05,
    load_rate=0.011, gen_rate=0.01, vre_rate=0.05,
    beta=0.67,
    reserve_exchange=false, budget_constraint = false)
    
    # SETS
    N = nodes.id
    G = generators.id
    V = vres.id
    Cac = schvacs.id
    Cdc = schvdcs.id
    P = periods.id
    A = areas.id
    Y = 1:years

    # INIT
    model = Model()
    set_optimizer(model, HiGHS.Optimizer)
    set_optimizer_attribute(model, "mip_rel_gap", epsilon)
    if silent
        set_silent(model)
    end

    # VARIABLES
    @variables(model, begin
        en[G,P,Y] >= 0
        vre[V,P,Y] >= 0
        ru[G,P,Y] >= 0
        rd[G,P,Y] >= 0
        ens[N,P,Y] >= 0
        runs[A,P,Y] >= 0
        rdns[A,P,Y] >= 0
        0 <= capac[Cac,Y] <= maxcap
        0 <= capdc[Cdc,Y] <= maxcap
        fac[Cac,P,Y]
        fdc[Cdc,P,Y]
        alphaac[Cac,Y], Bin
        alphadc[Cdc,Y], Bin
        theta[N,P,Y]
        budget[A,Y]
    end)
    for y in Y
        for p in P
            for slack in slacks
                fix(theta[slack,p,y],0,force=true)
            end
        end
    end
    
    # OBJECTIVE
    @expression(model, TCostOp[y in Y], 
        sum(periods[p,:w]*(generators[g,:encost]/generators[g,:efficiency]*en[g,p,y])
         for p in P for g in G) +
        sum(periods[p,:w]*(vres[v,:encost]*vre[v,p,y]) for p in P for v in V)
    )
    @expression(model, TCostAs[y in Y], 
        sum(periods[p,:w]*(
            generators[g,:rucost] / generators[g,:efficiency] *ru[g,p,y] +
            generators[g,:rdcost] / generators[g,:efficiency] *rd[g,p,y]
            ) for p in P for g in G
        )
    )
    @expression(model, TCostNs[y in Y],
        sum(periods[p,:w] * areas[a,:voll] * (ens[i,p,y] + runs[a,p,y] + rdns[a,p,y]) 
            for p in P for a in A for i in nodes[nodes.area.==a,:id])
    )
    @expression(model, TCostIntraInv[a in A, y in Y],
        sum(costacf * alphaac[l,y] for l in schvacs[schvacs.area.==a,:id]) +
        sum(costdcf * alphadc[l,y] for l in schvdcs[schvdcs.area.==a,:id]) +
        sum(costacv * schvacs[l,:length]*capac[l,y] for l in schvacs[schvacs.area.==a,:id]) +
        sum(costdcv * schvdcs[l,:length]*capdc[l,y] for l in schvdcs[schvdcs.area.==a,:id])
    )
    @expression(model, TCostCrossInv[y in Y],
        sum(costdcf * alphadc[l,y] for l in schvdcs[schvdcs.area.==0,:id]) +
        sum(costdcv * schvdcs[l,:length]*capdc[l,y] for l in schvdcs[schvdcs.area.==0,:id])
    )

    if budget_constraint
        @objective(model, Min, 
            sum((TCostOp[y] + TCostAs[y] + TCostNs[y]) / ((1 + d)^(y-1)) for y in Y)
        )
        @constraint(model, cBudget[a in A, y in Y], 
            sum(TCostIntraInv[a,zeta] + areas[a,:commitment] * TCostCrossInv[zeta] for zeta in minimum(Y):y) <= y * areas[a,:budget]
        )
    else
        @objective(model, Min, 
            sum(( sum(TCostIntraInv[a,y] for a in A) +
                TCostOp[y] + TCostAs[y] + TCostNs[y] + TCostCrossInv[y]) / ((1 + d)^(y-1))
                for y in Y
            )
        )
    end
        
    # CONSTRAINTS
    @constraint(model,cPowerBalance[i in N, p in P, y in Y],
        sum(en[g,p,y] for g in generators[generators.node.==i,:id]) +
        sum(vre[v,p,y] for v in vres[vres.node.==i,:id]) +
        sum(fac[l,p,y] for l in schvacs[schvacs.t_node.==i,:id]) -
        sum(fac[l,p,y] for l in schvacs[schvacs.f_node.==i,:id]) +
        sum(fdc[l,p,y] for l in schvdcs[schvdcs.t_node.==i,:id]) -
        sum(fdc[l,p,y] for l in schvdcs[schvdcs.f_node.==i,:id]) ==
        periods[p,"load$i"]*(1+load_rate)^(y-1) + ens[i,p,y]
    )
    @constraint(model, cPowerFlowExistMax[l in Cac, p in P, y in Y],
        fac[l,p,y] - 
        Sbase*(theta[schvacs[l,:f_node],p,y] - theta[schvacs[l,:t_node],p,y]) /
        schvacs[l,:x] <= bigM*(1 - schvacs[l,:existed])
    )
    @constraint(model, cPowerFlowExistMin[l in Cac, p in P, y in Y],
        fac[l,p,y] - 
        Sbase*(theta[schvacs[l,:f_node],p,y] - theta[schvacs[l,:t_node],p,y]) /
        schvacs[l,:x] >= -bigM*(1 - schvacs[l,:existed])
    )
    @constraint(model, cPowerFlowAlphaAcMax[l in Cac, p in P, y in Y],
        fac[l,p,y] - 
        Sbase*(theta[schvacs[l,:f_node],p,y] - theta[schvacs[l,:t_node],p,y]) /
        schvacs[l,:x] <= bigM*(1 - sum(alphaac[l,zeta] for zeta in minimum(Y):y))
    )
    @constraint(model, cPowerFlowAlphaAcMin[l in Cac, p in P, y in Y],
        fac[l,p,y] - 
        Sbase*(theta[schvacs[l,:f_node],p,y] - theta[schvacs[l,:t_node],p,y]) /
        schvacs[l,:x] >= -bigM*(1 - sum(alphaac[l,zeta] for zeta in minimum(Y):y))
    )
    @constraint(model, cACLimitMax[l in Cac, p in P, y in Y],
        fac[l,p,y] <= 
            schvacs[l,:existing_capacity] + sum(capac[l,zeta] for zeta in minimum(Y):y) + maxcap*(1 - sum(alphaac[l,zeta] for zeta in minimum(Y):y))
    )
    @constraint(model, cACLimitMin[l in Cac, p in P, y in Y],
        fac[l,p,y] >= 
            -(schvacs[l,:existing_capacity] + sum(capac[l,zeta] for zeta in minimum(Y):y) + maxcap*(1-sum(alphaac[l,zeta] for zeta in minimum(Y):y)))
    )
    @constraint(model, cACLimitMax2[l in Cac, p in P, y in Y],
        fac[l,p,y] <= 
            schvacs[l,:existing_capacity] + sum(alphaac[l,zeta] for zeta in minimum(Y):y)*maxcap
    )
    @constraint(model, cACLimitMin2[l in Cac, p in P, y in Y],
        fac[l,p,y] >= 
            -(schvacs[l,:existing_capacity] + sum(alphaac[l,zeta] for zeta in minimum(Y):y)*maxcap)
    )
    @constraint(model, cAlphaacForceCapac[l in Cac, y in Y],
        capac[l,y] <= maxcap * alphaac[l,y]
    )
    @constraint(model, cDCLimitMax[l in Cdc, p in P, y in Y],
        fdc[l,p,y] <= 
            schvdcs[l,:existing_capacity] + sum(capdc[l,zeta] for zeta in minimum(Y):y) + maxcap*(1 - sum(alphadc[l,zeta] for zeta in minimum(Y):y))
    )
    @constraint(model, cDCLimitMin[l in Cdc, p in P, y in Y],
        fdc[l,p,y] >= 
            -(schvdcs[l,:existing_capacity] + sum(capdc[l,zeta] for zeta in minimum(Y):y) + maxcap*(1 - sum(alphadc[l,zeta] for zeta in minimum(Y):y)))
    )
    @constraint(model, cDCLimitMax2[l in Cdc, p in P, y in Y],
        fdc[l,p,y] <= 
            schvdcs[l,:existing_capacity] + maxcap*(sum(alphadc[l,zeta] for zeta in minimum(Y):y))
    )
    @constraint(model, cDCLimitMin2[l in Cdc, p in P, y in Y],
        fdc[l,p,y] >= 
            -(schvdcs[l,:existing_capacity] + maxcap*(sum(alphadc[l,zeta] for zeta in minimum(Y):y)))
    )
    @constraint(model, cAlphadcForceCapdc[l in Cdc, y in Y],
        capdc[l,y] <= maxcap * alphadc[l,y]
    )
    @constraint(model,cMaxLimitGen[g in G, p in P, y in Y],
        en[g,p,y] + ru[g,p,y] <= generators[g,:pmax] * generators[g,:pu_max] * (1 + gen_rate)^(y-1)
    )
    @constraint(model,cMinlLimitGen[g in G, p in P, y in Y],
        en[g,p,y] - rd[g,p,y] >= generators[g,:pmax] * generators[g,:pu_min]
    )
    @constraint(model,cMaxLimitVre[v in V, p in P, y in Y],
        vre[v,p,y] <= periods[p,"$(vres[v,:type])$(vres[v,:node])"]*vres[v,:pmax] * (1 + vre_rate)^(y-1)
    )
    @constraint(model,cAlphaAcSumEqualsOne[l in Cac],
        sum(alphaac[l,y] for y in Y) <= 1
    )
    @constraint(model,cAlphaDcSumEqualsOne[l in Cdc],
        sum(alphadc[l,y] for y in Y) <= 1
    )
    if reserve_exchange
        @constraint(model,cReserveRequirementRU[a in A, p in P, y in Y],
            sum(ru[g,p,y] for g in generators[generators.area.==a,:id]) >= beta * areas[a,:reqru]
            - runs[a,p,y]
        )
        @constraint(model,cReserveRequirementRD[a in A, p in P, y in Y],
            sum(rd[g,p,y] for g in generators[generators.area.==a,:id]) >= beta * areas[a,:reqrd]
            - rdns[a,p,y]
        )
        @constraint(model, cRRRU2[p in P, y in Y],
            sum(ru[g,p,y] for g in G) >= sum(areas.reqru) + sum(runs[a,p,y] for a in A)
        )
        @constraint(model, cRRRD2[p in P, y in Y],
            sum(rd[g,p,y] for g in G) >= sum(areas.reqrd) + sum(rdns[a,p,y] for a in A)
        )
        @constraint(model, cNetRU[a in A, p in P, y in Y],
            sum(ru[g,p,y] + en[g,p,y] for g in generators[generators.area.==a,:id]) + sum(vre[v,p,y] for v in vres[vres.area.==a,:id]) - sum(periods[p,"load$i"]*(1+load_rate)^(y-1) + ens[i,p,y] for i in nodes[nodes.area.==a,:id]) - areas[a,:reqru] - runs[a,p,y]  <=
            sum(schvdcs[schvdcs.area.==0,:][schvdcs[schvdcs.area.==0,:].f_area.==a,:existing_capacity]) + 
            sum(schvdcs[schvdcs.area.==0,:][schvdcs[schvdcs.area.==0,:].t_area.==a,:existing_capacity]) +
            sum(sum(capdc[l,zeta] for l in schvdcs[schvdcs.area.==0,:][schvdcs[schvdcs.area.==0,:].f_area.==a,:id]) for zeta in minimum(Y):y) +
            sum(sum(capdc[l,zeta] for l in schvdcs[schvdcs.area.==0,:][schvdcs[schvdcs.area.==0,:].t_area.==a,:id]) for zeta in minimum(Y):y) 
        )
        @constraint(model, cNetRD[a in A, p in P, y in Y],
            sum(rd[g,p,y] - en[g,p,y] for g in generators[generators.area.==a,:id]) - sum(vre[v,p,y] for v in vres[vres.area.==a,:id]) + sum(periods[p,"load$i"]*(1+load_rate)^(y-1) + ens[i,p,y] for i in nodes[nodes.area.==a,:id]) - areas[a,:reqrd] - rdns[a,p,y]  <=
            sum(schvdcs[schvdcs.area.==0,:][schvdcs[schvdcs.area.==0,:].f_area.==a,:existing_capacity]) + 
            sum(schvdcs[schvdcs.area.==0,:][schvdcs[schvdcs.area.==0,:].t_area.==a,:existing_capacity]) +
            sum(sum(capdc[l,zeta] for l in schvdcs[schvdcs.area.==0,:][schvdcs[schvdcs.area.==0,:].f_area.==a,:id]) for zeta in minimum(Y):y) +
            sum(sum(capdc[l,zeta] for l in schvdcs[schvdcs.area.==0,:][schvdcs[schvdcs.area.==0,:].t_area.==a,:id]) for zeta in minimum(Y):y) 
        )
    else   
        @constraint(model,cReserveRequirementRU[a in A, p in P, y in Y],
            sum(ru[g,p,y] for g in generators[generators.area.==a,:id]) >= areas[a,:reqru]
            + runs[a,p,y]
        )
        @constraint(model,cReserveRequirementRD[a in A, p in P, y in Y],
            sum(rd[g,p,y] for g in generators[generators.area.==a,:id]) >= areas[a,:reqrd]
            + rdns[a,p,y]
        )
    end

    # SOLVE
    optimize!(model)

    return(
        Obj = objective_value(model),
        TCostOp = value.(TCostOp),
        TCostAs = value.(TCostAs),
        TCostNs = value.(TCostNs),
        TCostIntraInv = value.(TCostIntraInv),
        TCostCrossInv = value.(TCostCrossInv),
        en = value.(en).data,
        vre = value.(vre).data,
        ru = value.(ru).data,
        rd = value.(rd).data,
        ens = value.(ens).data,
        runs = value.(runs).data,
        rdns = value.(rdns).data,
        capac = value.(capac).data,
        capdc = value.(capdc).data,
        fac = value.(fac).data,
        fdc = value.(fdc).data,
        alphaac = value.(alphaac).data,
        alphadc = value.(alphadc).data,
        theta = value.(theta).data,
        budget = value.(budget).data,
    )
end