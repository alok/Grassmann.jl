
#   This file is part of Grassmann.jl. It is licensed under the AGPL license
#   Grassmann Copyright (C) 2019 Michael Reed

@pure tvec(N,G,t::Symbol=:Any) = :(Values{$(binomial(N,G)),$t})
@pure tvec(N,t::Symbol=:Any) = :(Values{$(1<<N),$t})
@pure tvec(N,μ::Bool) = tvec(N,μ ? :Any : :t)

# mutating operations

@pure derive(n::N,b) where N<:Number = zero(typeof(n))
derive(n,b,a,t) = t ? (a,derive(n,b)) : (derive(n,b),a)
#derive(n,b,a::T,t) where T<:TensorAlgebra = t ? (a,derive(n,b)) : (derive(n,b),a)

@inline function derive_mul(V,A,B,v,x::Bool)
    if !(istangent(V) && isdyadic(V))
        return v
    else
        sa,sb = symmetricsplit(V,A),symmetricsplit(V,B)
        ca,cb = count_ones(sa[2]),count_ones(sb[2])
        return if (ca == cb == 0) || ((ca ≠ 0) && (cb ≠ 0))
            v
        else
            prev = ca == 0 ? (x ? one(typeof(v)) : v) : (x ? v : one(typeof(v)))
            for k ∈ Leibniz.indexsplit((ca==0 ? sa : sb)[1],mdims(V))
                prev = derive(prev,getbasis(V,k))
            end
            prev
        end
    end
end

@inline function derive_mul(V,A,B,a,b,*)
    if !(istangent(V) && isdyadic(V))
        return a*b
    else
        sa,sb = symmetricsplit(V,A),symmetricsplit(V,B)
        ca,cb = count_ones(sa[2]),count_ones(sb[2])
        α,β = if (ca == cb == 0) || ((ca ≠ 0) && (cb ≠ 0))
            a,b
        else
            prev = ca == 0 ? (a,b) : (b,a)
            for k ∈ Leibniz.indexsplit((ca==0 ? sa : sb)[1],mdims(V))
                prev = derive(prev[2],getbasis(V,k),prev[1],true)
            end
            #base = getbasis(V,0)
            while typeof(prev[1]) <: TensorTerm
                basi = basis(prev[1])
                #base *= basi
                inds = Leibniz.indexsplit(bits(basi),mdims(V))
                prev = (value(prev[1]),prev[2])
                for k ∈ inds
                    prev = derive(prev[2],getbasis(V,k),prev[1],true)
                end
            end
            #base ≠ getbasis(V,0) && (prev = (base*prev[1],prev[2]))
            ca == 0 ? prev : (prev[2],prev[1])
        end
        return α*β
    end
end

function derive_pre(V,A,B,v,x)
    if !(istangent(V) && isdyadic(V))
        return v
    else
        return :(derive_post($V,$(Val{A}()),$(Val{B}()),$v,$x))
    end
end

function derive_pre(V,A,B,a,b,p)
    if !(istangent(V) && isdyadic(V))
        return Expr(:call,p,a,b)
    else
        return :(derive_post($V,$(Val{A}()),$(Val{B}()),$a,$b,$p))
    end
end

function derive_post(V,::Val{A},::Val{B},v,x::Bool) where {A,B}
    sa,sb = symmetricsplit(V,A),symmetricsplit(V,B)
    ca,cb = count_ones(sa[2]),count_ones(sb[2])
    return if (ca == cb == 0) || ((ca ≠ 0) && (cb ≠ 0))
        v
    else
        prev = ca == 0 ? (x ? one(typeof(v)) : v) : (x ? v : one(typeof(v)))
        for k ∈ Leibniz.indexsplit((ca==0 ? sa : sb)[1],mdims(V))
            prev = derive(prev,getbasis(V,k))
        end
        prev
    end
end

function derive_post(V,::Val{A},::Val{B},a,b,*) where {A,B}
    sa,sb = symmetricsplit(V,A),symmetricsplit(V,B)
    ca,cb = count_ones(sa[2]),count_ones(sb[2])
    α,β = if (ca == cb == 0) || ((ca ≠ 0) && (cb ≠ 0))
        a,b
    else
        prev = ca == 0 ? (a,b) : (b,a)
        for k ∈ Leibniz.indexsplit((ca==0 ? sa : sb)[1],mdims(V))
            prev = derive(prev[2],getbasis(V,k),prev[1],true)
        end
        #base = getbasis(V,0)
        while typeof(prev[1]) <: TensorTerm
            basi = basis(prev[1])
            #base *= basi
            inds = Leibniz.indexsplit(bits(basi),mdims(V))
            prev = (value(prev[1]),prev[2])
            for k ∈ inds
                prev = derive(prev[2],getbasis(V,k),prev[1],true)
            end
        end
        #base ≠ getbasis(V,0) && (prev = (base*prev[1],prev[2]))
        ca == 0 ? prev : (prev[2],prev[1])
    end
    return α*β
end

bcast(op,arg) = op ∈ (:(AbstractTensors.:∑),:(AbstractTensors.:-)) ? Expr(:.,op,arg) : Expr(:call,op,arg.args...)

set_val(set,expr,val) = Expr(:(=),expr,set≠:(=) ? Expr(:call,:($Sym.:∑),expr,val) : val)

pre_val(set,expr,val) = set≠:(=) ? :(isnull($expr) ? ($expr=Expr(:call,:($Sym.:∑),$val)) : push!($expr.args,$val)) : Expr(:(=),expr,val)

add_val(set,expr,val,OP) = Expr(OP∉(:-,:+) ? :.= : set,expr,OP∉(:-,:+) ? Expr(:.,OP,Expr(:tuple,expr,val)) : val)

function generate_mutators(M,F,set_val,SUB,MUL,i,B)
    for (op,set) ∈ ((:add,:(+=)),(:set,:(=)))
        sm = Symbol(op,:multi!)
        sb = Symbol(op,:blade!)
        for (s,index) ∈ ((sm,:basisindex),(sb,:bladeindex))
            spre = Symbol(s,:_pre)
            @eval begin
                @inline function $s(out::$M,val::S,i::$B) where {M,T<:$F,S<:$F}
                    @inbounds $(set_val(set,:(out[$index(intlog(M),$i)]),:val))
                    return out
                end
                @inline function $s(out::Q,val::S,i::$B,::Val{N}) where Q<:$M where {M,T<:$F,S<:$F,N}
                    @inbounds $(set_val(set,:(out[$index(N,$i)]),:val))
                    return out
                end
                @inline function $spre(out::$M,val::S,i::$B) where {M,T<:$F,S<:$F}
                    ind = $index(intlog(M),$i)
                    @inbounds $(pre_val(set,:(out[ind]),:val))
                    return out
                end
                @inline function $spre(out::Q,val::S,i::$B,::Val{N}) where Q<:$M where {M,T<:$F,S<:$F,N}
                    ind = $index(N,$i)
                    @inbounds $(pre_val(set,:(out[ind]),:val))
                    return out
                end
            end
        end
    end
end

function generate_mutators(M,F,set_val,SUB,MUL)
    generate_mutators(M,F,set_val,SUB,MUL,:i,UInt)
    generate_mutators(M,F,set_val,SUB,MUL,:(UInt(i)),SubManifold)
    for (op,set) ∈ ((:add,:(+=)),(:set,:(=)))
        sm = Symbol(op,:multi!)
        sb = Symbol(op,:blade!)
        for (s,index) ∈ ((sm,:basisindex),(sb,:bladeindex))
            spre = Symbol(s,:_pre)
            @eval @inline function $s(out::$M,val::S,i) where {M,T,S}
                @inbounds $(set_val(set,:(out[i]),:val))
                return out
            end
        end
        for s ∈ (sm,sb)
            spre = Symbol(s,:_pre)
            for j ∈ (:join,:geom)
                for S ∈ (s,spre)
                    @eval @inline function $(Symbol(j,S))(m::$M,v::S,A::SubManifold{V},B::SubManifold{V}) where {V,T<:$F,S<:$F,M}
                        $(Symbol(j,S))(V,m,bits(A),bits(B),v)
                    end
                end
            end
            @eval begin
                @inline function $(Symbol(:join,s))(V,m::$M,a::UInt,b::UInt,v::S) where {T<:$F,S<:$F,M}
                    if v ≠ 0 && !diffcheck(V,a,b)
                        A,B,Q,Z = symmetricmask(V,a,b)
                        #val = (typeof(V)<:Signature || count_ones(A&B)==0) ? (parity(V,A,B) ? $SUB(v) : v) :
                        val = $MUL(parityinner(V,A,B),v)
                        if diffvars(V)≠0
                            !iszero(Z) && (T≠Any ? (return true) : (val *= getbasis(loworder(V),Z)))
                            count_ones(Q)+order(val)>diffmode(V) && (return false)
                        end
                        $s(m,val,(A⊻B)|Q,Val(mdims(V)))
                    end
                    return false
                end
                @inline function $(Symbol(:join,spre))(V,m::$M,a::UInt,b::UInt,v::S) where {T<:$F,S<:$F,M}
                    if v ≠ 0 && !diffcheck(V,a,b)
                        A,B,Q,Z = symmetricmask(V,a,b)
                        #val = (typeof(V)<:Signature || count_ones(A&B)==0) ? (parity(V,A,B) ? :($$SUB($v)) : v) :
                        val = :($$MUL($(parityinner(V,A,B)),$v))
                        if diffvars(V)≠0
                            !iszero(Z) && (val = Expr(:call,:*,val,getbasis(loworder(V),Z)))
                            val = :(h=$val;iszero(h)||$(count_ones(Q))+order(h)>$(diffmode(V)) ? 0 : h)
                        end
                        $spre(m,val,(A⊻B)|Q,Val(mdims(V)))
                    end
                    return false
                end
                @inline function $(Symbol(:geom,s))(V,m::$M,a::UInt,b::UInt,v::S) where {T<:$F,S<:$F,M}
                    if v ≠ 0 && !diffcheck(V,a,b)
                        A,B,Q,Z = symmetricmask(V,a,b)
                        pcc,bas,cc = (hasinf(V) && hasorigin(V)) ? conformal(V,A,B) : (false,A⊻B,false)
                        #val = (typeof(V)<:Signature || count_ones(A&B)==0) ? (parity(V,A,B)⊻pcc ? $SUB(v) : v) :
                        val = $MUL(parityinner(V,A,B),pcc ? $SUB(v) : v)
                        if istangent(V)
                            !iszero(Z) && (T≠Any ? (return true) : (val *= getbasis(loworder(V),Z)))
                            count_ones(Q)+order(val)>diffmode(V) && (return false)
                        end
                        $s(m,val,bas|Q,Val(mdims(V)))
                        cc && $s(m,hasinforigin(V,A,B) ? $SUB(val) : val,(conformalmask(V)⊻bas)|Q,Val(mdims(V)))
                    end
                    return false
                end
                @inline function $(Symbol(:geom,spre))(V,m::$M,a::UInt,b::UInt,v::S) where {T<:$F,S<:$F,M}
                    if v ≠ 0 && !diffcheck(V,a,b)
                        A,B,Q,Z = symmetricmask(V,a,b)
                        pcc,bas,cc = (hasinf(V) && hasorigin(V)) ? conformal(V,A,B) : (false,A⊻B,false)
                        #val = (typeof(V)<:Signature || count_ones(A&B)==0) ? (parity(V,A,B)⊻pcc ? :($$SUB($v)) : v) :
                        val = :($$MUL($(parityinner(V,A,B)),$(pcc ? :($$SUB($v)) : v)))
                        if istangent(V)
                            !iszero(Z) && (val = Expr(:call,:*,val,getbasis(loworder(V),Z)))
                            val = :(h=$val;iszero(h)||$(count_ones(Q))+order(h)>$(diffmode(V)) ? 0 : h)
                        end
                        $spre(m,val,bas|Q,Val(mdims(V)))
                        cc && $spre(m,hasinforigin(V,A,B) ? :($$SUB($val)) : val,(conformalmask(V)⊻bas)|Q,Val(mdims(V)))
                    end
                    return false
                end
            end
            for (prod,uct) ∈ ((:meet,:regressive),(:skew,:interior))
                for S ∈ (s,spre)
                    @eval @inline function $(Symbol(prod,S))(m::$M,A::SubManifold{V},B::SubManifold{V},v::T) where {V,T,M}
                        $(Symbol(prod,S))(V,m,bits(A),bits(B),v)
                    end
                end
                @eval begin
                    @inline function $(Symbol(prod,s))(V,m::$M,A::UInt,B::UInt,val::T) where {T,M}
                        if val ≠ 0
                            g,C,t,Z = $uct(V,A,B)
                            v = val
                            if istangent(V)
                                if !iszero(Z)
                                    T≠Any && (return true)
                                    _,_,Q,_ = symmetricmask(V,A,B)
                                    v *= getbasis(loworder(V),Z)
                                    count_ones(Q)+order(v)>diffmode(V) && (return false)
                                end
                            end
                            t && $s(m,typeof(V) <: Signature ? g ? $SUB(v) : v : $MUL(g,v),C,Val(mdims(V)))
                        end
                        return false
                    end
                    @inline function $(Symbol(prod,spre))(V,m::$M,A::UInt,B::UInt,val::T) where {T,M}
                        if val ≠ 0
                            g,C,t,Z = $uct(V,A,B)
                            v = val
                            if istangent(V)
                                if !iszero(Z)
                                    _,_,Q,_ = symmetricmask(V,A,B)
                                    v = Expr(:call,:*,v,getbasis(loworder(V),Z))
                                    v = :(h=$v;iszero(h)||$(count_ones(Q))+order(h)>$(diffmode(V)) ? 0 : h)
                                end
                            end
                            t && $spre(m,typeof(V) <: Signature ? g ? :($$SUB($v)) : v : Expr(:call,$(QuoteNode(MUL)),g,v),C,Val(mdims(V)))
                        end
                        return false
                    end
                end
            end
        end
    end
end

@inline exterbits(V,α,β) = diffvars(V)≠0 ? ((a,b)=symmetricmask(V,α,β);count_ones(a&b)==0) : count_ones(α&β)==0
@inline exteraddmulti!(V,out,α,β,γ) = exterbits(V,α,β) && joinaddmulti!(V,out,α,β,γ)
@inline exteraddblade!(V,out,α,β,γ) = exterbits(V,α,β) && joinaddblade!(V,out,α,β,γ)
@inline exteraddmulti!_pre(V,out,α,β,γ) = exterbits(V,α,β) && joinaddmulti!_pre(V,out,α,β,γ)
@inline exteraddblade!_pre(V,out,α,β,γ) = exterbits(V,α,β) && joinaddblade!_pre(V,out,α,β,γ)

# algebra

@eval begin
    *(a::F,b::MultiVector{V,T}) where {F<:Number,V,T} = MultiVector{V,promote_type(T,F)}(broadcast($Sym.:∏,Ref(a),b.v))
    *(a::MultiVector{V,T},b::F) where {F<:Number,V,T} = MultiVector{V,promote_type(T,F)}(broadcast($Sym.:∏,a.v,Ref(b)))
    *(a::F,b::Chain{V,G,T}) where {F<:Number,V,G,T} = Chain{V,G,promote_type(T,F)}(broadcast($Sym.:∏,Ref(a),b.v))
    *(a::Chain{V,G,T},b::F) where {F<:Number,V,G,T,} = Chain{V,G,promote_type(T,F)}(broadcast($Sym.:∏,a.v,Ref(b)))
    *(a::F,b::Simplex{V,G,B,T} where B) where {F<:Number,V,G,T} = Simplex{V,G}($Sym.:∏(a,b.v),basis(b))
    *(a::Simplex{V,G,B,T} where B,b::F) where {F<:Number,V,G,T} = Simplex{V,G}($Sym.:∏(a.v,b),basis(a))
end

for F ∈ Fields
    @eval begin
        *(a::F,b::MultiVector{V,T}) where {F<:$F,V,T<:Number} = MultiVector{V,promote_type(T,F)}(broadcast(*,Ref(a),b.v))
        *(a::MultiVector{V,T},b::F) where {F<:$F,V,T<:Number} = MultiVector{V,promote_type(T,F)}(broadcast(*,a.v,Ref(b)))
        *(a::F,b::Chain{V,G,T}) where {F<:$F,V,G,T<:Number} = Chain{V,G,promote_type(T,F)}(broadcast(*,Ref(a),b.v))
        *(a::Chain{V,G,T},b::F) where {F<:$F,V,G,T<:Number} = Chain{V,G,promote_type(T,F)}(broadcast(*,a.v,Ref(b)))
        *(a::F,b::Simplex{V,G,B,T} where B) where {F<:$F,V,G,T<:Number} = Simplex{V,G}(*(a,b.v),basis(b))
        *(a::Simplex{V,G,B,T} where B,b::F) where {F<:$F,V,G,T<:Number} = Simplex{V,G}(*(a.v,b),basis(a))
    end
end

for A ∈ (SubManifold,Simplex,Chain,MultiVector)
    for B ∈ (SubManifold,Simplex,Chain,MultiVector)
        @eval @inline *(a::$A,b::$B) = interop(*,a,b)
    end
end

for un ∈ (:complementleft,:complementright)
    @eval begin
        $un(t::SparseChain{V,G}) where {V,G} = SparseChain{V,mdims(V)-G}($un.(terms(t)))
        $un(t::MultiGrade{V,G}) where {V,G} = SparseChain{V,G⊻(UInt(1)<<mdims(V)-1)}(reverse($un.(terms(t))))
    end
end
for un ∈ (:reverse,:involute,:conj,:+,:-)
    @eval begin
        $un(t::SparseChain{V,G}) where {V,G} = SparseChain{V,G}($un.(terms(t)))
        $un(t::MultiGrade{V,G}) where {V,G} = SparseChain{V,G}($un.(terms(t)))
    end
end

const FieldsBig = (Fields...,BigFloat,BigInt,Complex{BigFloat},Complex{BigInt},Rational{BigInt})

function generate_sums(Field=Field,VEC=:mvec,MUL=:*,ADD=:+,SUB=:-,CONJ=:conj,PAR=false)
    if Field == Grassmann.Field
        generate_mutators(:(Variables{M,T}),Number,Expr,SUB,MUL)
    elseif Field ∈ (SymField,:(SymPy.Sym))
        generate_mutators(:(FixedVector{M,T}),Field,set_val,SUB,MUL)
    end
    PAR && (DirectSum.extend_field(eval(Field)); global parsym = (parsym...,eval(Field)))
    TF = Field ∉ FieldsBig ? :Any : :T
    EF = Field ≠ Any ? Field : ExprField
    Field ∉ Fields && @eval begin
        *(a::F,b::SubManifold{V}) where {F<:$EF,V} = Simplex{V}(a,b)
        *(a::SubManifold{V},b::F) where {F<:$EF,V} = Simplex{V}(b,a)
        *(a::F,b::Simplex{V,G,B,T} where B) where {F<:$Field,V,G,T<:$Field} = Simplex{V,G}($MUL(a,b.v),basis(b))
        *(a::Simplex{V,G,B,T} where B,b::F) where {F<:$Field,V,G,T<:$Field} = Simplex{V,G}($MUL(a.v,b),basis(a))
        adjoint(b::Simplex{V,G,B,T}) where {V,G,B,T<:$Field} = Simplex{dual(V),G,B',$TF}($CONJ(value(b)))
        Base.promote_rule(::Type{Simplex{V,G,B,T}},::Type{S}) where {V,G,T,B,S<:$Field} = Simplex{V,G,B,promote_type(T,S)}
        Base.promote_rule(::Type{Chain{V,G,T,B}},::Type{S}) where {V,G,T,B,S<:$Field} = Chain{V,G,promote_type(T,S),B}
        Base.promote_rule(::Type{MultiVector{V,T,B}},::Type{S}) where {V,T,B,S<:$Field} = MultiVector{V,promote_type(T,S),B}
    end
    @eval begin
        *(a::F,b::Chain{V,G,T}) where {F<:$Field,V,G,T<:$Field} = Chain{V,G}(broadcast($MUL,Ref(a),b.v))
        *(a::Chain{V,G,T},b::F) where {F<:$Field,V,G,T<:$Field} = Chain{V,G}(broadcast($MUL,a.v,Ref(b)))
        *(a::F,b::MultiVector{V,T}) where {F<:$Field,T,V} = MultiVector{V}(broadcast($Sym.∏,Ref(a),b.v))
        *(a::MultiVector{V,T},b::F) where {F<:$Field,T,V} = MultiVector{V}(broadcast($Sym.∏,a.v,Ref(b)))
        -(a::Chain{V,G,T}) where {V,G,T<:$Field} = Chain{V,G,$TF}($(bcast(SUB,:(value(a),))))
        -(a::MultiVector{V,T}) where {V,T<:$Field} = MultiVector{V,$TF}($(bcast(SUB,:(value(a),))))
        *(a::Simplex{V,0,B,F},b::Chain{V,G,T}) where {F<:$Field,B,V,G,T<:$Field} = Chain{V,G}(broadcast($MUL,Ref(a.v),b.v))
        *(a::Chain{V,G,T},b::Simplex{V,0,B,F}) where {F<:$Field,B,V,G,T<:$Field} = Chain{V,G}(broadcast($MUL,a.v,Ref(b.v)))
        *(a::SubManifold{V,0},b::Chain{W,G,T}) where {V,W,G,T<:$Field} = b
        *(a::Chain{V,G,T},b::SubManifold{W,0}) where {V,W,G,T<:$Field} = a
        *(a::F,b::MultiGrade{V,G}) where {F<:$EF,V,G} = MultiGrade{V,G}(broadcast($MUL,Ref(a),b.v))
        *(a::MultiGrade{V,G},b::F) where {F<:$EF,V,G} = MultiGrade{V,G}(broadcast($MUL,a.v,Ref(b)))
        Base.:-(a::Simplex{V,G,B,T}) where {V,G,B,T<:$Field} = Simplex{V,G,B,$TF}(SUB(value(a)))
        @generated function Base.adjoint(m::Chain{V,G,T}) where {V,G,T<:$Field}
            if binomial(mdims(V),G)<(1<<cache_limit)
                if isdyadic(V)
                    $(insert_expr((:N,:M,:ib),:svec)...)
                    out = zeros(svec(N,G,Any))
                    for i ∈ 1:binomial(N,G)
                        @inbounds setblade!_pre(out,:($$CONJ(m.v[$i])),dual(V,ib[i],M),Val{N}())
                    end
                    return :(Chain{$(dual(V)),G}($(Expr(:call,tvec(N,TF),out...))))
                else
                    return :(Chain{$(dual(V)),G}($$CONJ.(value(m))))
                end
            else return quote
                if isdyadic(V)
                    $(insert_expr((:N,:M,:ib),$(QuoteNode(VEC)))...)
                    out = zeros($$VEC(N,G,$$TF))
                    for i ∈ 1:binomial(N,G)
                        @inbounds setblade!(out,$$CONJ(m.v[i]),dual(V,ib[i],M),Val{N}())
                    end
                else
                    out = $$CONJ.(value(m))
                end
                Chain{dual(V),G}(out)
            end end
        end
        @generated function Base.adjoint(m::MultiVector{V,T}) where {V,T<:$Field}
            if mdims(V)<cache_limit
                if isdyadic(V)
                    $(insert_expr((:N,:M,:bs,:bn),:svec)...)
                    out = zeros(svec(N,Any))
                    for g ∈ 1:N+1
                        ib = indexbasis(N,g-1)
                        @inbounds for i ∈ 1:bn[g]
                            @inbounds setmulti!_pre(out,:($$CONJ(m.v[$(bs[g]+i)])),dual(V,ib[i],M))
                        end
                    end
                    return :(MultiVector{$(dual(V))}($(Expr(:call,tvec(N,TF),out...))))
                else
                    return :(MultiVector{$(dual(V))}($$CONJ.(value(m))))
                end
            else return quote
                if isdyadic(V)
                    $(insert_expr((:N,:M,:bs,:bn),$(QuoteNode(VEC)))...)
                    out = zeros($$VEC(N,$$TF))
                    for g ∈ 1:N+1
                        ib = indexbasis(N,g-1)
                        @inbounds for i ∈ 1:bn[g]
                            @inbounds setmulti!(out,$$CONJ(m.v[bs[g]+i]),dual(V,ib[i],M))
                        end
                    end
                else
                    out = $$CONJ.(value(m))
                end
                MultiVector{dual(V)}(out)
            end end
        end
    end
    for (op,eop,bop) ∈ ((:+,:(+=),ADD),(:-,:(-=),SUB))
        @eval begin
            function $op(a::Chain{V,G,T},b::Chain{V,L,S}) where {V,G,T<:$Field,L,S<:$Field}
                $(insert_expr((:N,:t,:out,:r,:bng),VEC)...)
                @inbounds out[r+1:r+bng] = value(a,$VEC(N,G,t))
                rb = binomsum(N,L)
                Rb = binomial(N,L)
                @inbounds out[rb+1:rb+Rb] = $(bcast(bop,:(value(b,$VEC(N,L,t)),)))
                return MultiVector{V}(out)
            end
            function $op(a::Chain{V,G,T},b::Chain{V,G,S}) where {V,G,T<:$Field,S<:$Field}
                return Chain{V,G,promote_type(valuetype(a),valuetype(b))}($(bcast(bop,:(a.v,b.v))))
            end
            function $op(a::MultiVector{V,T},b::MultiVector{V,S}) where {V,T<:$Field,S<:$Field}
                $(insert_expr((:N,:t),VEC)...)
                out = copy(value(a,$VEC(N,t)))
                $(add_val(eop,:out,:(value(b,$VEC(N,t))),bop))
                return MultiVector{V}(out)
            end
            function $op(a::SparseChain{V,G,S},b::MultiVector{V,T}) where {V,T<:$Field,G,S<:$Field}
                $(insert_expr((:N,:t),VEC)...)
                at = value(a)
                out = convert($VEC(N,t),$(bcast(bop,:(copy(value(b,$VEC(N,t))),))))
                addmulti!(out,at.nzval,binomsum(N,G).+at.nzind)
                return MultiVector{V}(out)
            end
            function $op(a::MultiVector{V,T},b::SparseChain{V,G}) where {V,T<:$Field,G}
                $(insert_expr((:N,:t),VEC)...)
                bt = value(b)
                out = copy(value(a,$VEC(N,t)))
                addmulti!(out,$bop.(bt.nzval),binomsum(N,G).+bt.nzind)
                return MultiVector{V}(out)
            end
            function $op(a::Chain{V,G,T},b::SparseChain{V,G}) where {V,G,T<:$Field}
                $(insert_expr((:N,),VEC)...)
                bt = terms(b)
                t = promote_type(T,valuetype.(bt)...)
                out = copy(value(a,$VEC(N,G,t)))
                addmulti!(out,bt.nzval,bt.nzind)
                return Chain{V,G}(out)
            end
            function $op(a::SparseChain{V,G},b::Chain{V,G,T}) where {V,G,T<:$Field}
                $(insert_expr((:N,),VEC)...)
                at = terms(a)
                t = promote_type(T,valuetype.(at)...)
                out = convert($VEC(N,G,t),$(bcast(bop,:(copy(value(b,$VEC(N,G,t))),))))
                addmulti!(out,at.nzval,at.nzind)
                return Chain{V,G}(out)
            end
            function $op(a::Chain{V,G,T},b::MultiVector{V,S}) where {V,G,T<:$Field,S<:$Field}
                $(insert_expr((:N,:t,:r,:bng),VEC)...)
                out = convert($VEC(N,t),$(bcast(bop,:(copy(value(b,$VEC(N,t))),))))
                @inbounds $(add_val(:(+=),:(out[r+1:r+bng]),:(value(a,$VEC(N,G,t))),ADD))
                return MultiVector{V}(out)
            end
            function $op(a::MultiVector{V,T},b::Chain{V,G,S}) where {V,T<:$Field,G,S<:$Field}
                $(insert_expr((:N,:t,:r,:bng),VEC)...)
                out = copy(value(a,$VEC(N,t)))
                @inbounds $(add_val(eop,:(out[r+1:r+bng]),:(value(b,$VEC(N,G,t))),bop))
                return MultiVector{V}(out)
            end
            function $op(a::MultiGrade{V,G},b::MultiVector{V,T}) where {V,T<:$Field,G}
                $(insert_expr((:N,),VEC)...)
                at = terms(a)
                t = promote_type(T,valuetype.(at)...)
                out = convert($VEC(N,t),$(bcast(bop,:(value(b,$VEC(N,t)),))))
                for A ∈ at
                    TA = typeof(A)
                    if TA <: TensorTerm
                        addmulti!(out,value(A,t),bits(A),Val{N}())
                    elseif TA <: SparseChain
                        vA = value(A,t)
                        addmulti!(out,vA.nzval,vA.nzind)
                    else
                        g = rank(A)
                        r = binomsum(N,g)
                        @inbounds $(add_val(eop,:(out[r+1:r+binomial(N,g)]),:(value(A,$VEC(N,g,t))),bop))
                    end
                end
                return MultiVector{V}(out)
            end
            function $op(a::MultiVector{V,T},b::MultiGrade{V,G}) where {V,T<:$Field,G}
                $(insert_expr((:N,),VEC)...)
                bt = terms(b)
                t = promote_type(T,valuetype.(bt)...)
                out = value(a,$VEC(N,t))
                for B ∈ bt
                    TB = typeof(B)
                    if TB <: TensorTerm
                        addmulti!(out,$bop(value(B,t)),bits(B),Val{N}())
                    elseif TB <: SparseChain
                        vB = value(B,t)
                        addmulti!(out,vB.nzval,vB.nzind)
                    else
                        g = rank(B)
                        r = binomsum(N,g)
                        @inbounds $(add_val(eop,:(out[r+1:r+binomial(N,g)]),:(value(B,$VEC(N,g,t))),bop))
                    end
                end
                return MultiVector{V}(out)
            end
            @generated function $op(a::SubManifold{V,A,X},b::Simplex{V,B,Y,S}) where {V,A,X,B,Y,S<:$Field}
                adder(a,b,$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
            @generated function $op(a::Simplex{V,A,X,T},b::SubManifold{V,B,Y}) where {V,A,X,T<:$Field,B,Y}
                adder(a,b,$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
            @generated function $op(a::Simplex{V,A,X,T},b::Simplex{V,B,Y,S}) where {V,A,X,T<:$Field,B,Y,S<:$Field}
                adder(a,b,$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
            @generated function $op(a::SubManifold{V,G},b::Chain{V,G,T}) where {V,G,T<:$Field}
                adder(a,b,$(QuoteNode(ADD)),$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
            @generated function $op(a::Simplex{V,G,A,S} where A,b::Chain{V,G,T}) where {V,G,T<:$Field,S<:$Field}
                adder(a,b,$(QuoteNode(ADD)),$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
            @generated function $op(a::SubManifold{V,L},b::Chain{V,G,T}) where {V,G,T<:$Field,L}
                adder(a,b,$(QuoteNode(ADD)),$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
            @generated function $op(a::Simplex{V,L,A,S} where A,b::Chain{V,G,T}) where {V,G,T<:$Field,L,S<:$Field}
                adder(a,b,$(QuoteNode(ADD)),$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
            @generated function $op(a::SubManifold{V,G},b::MultiVector{V,T}) where {V,T<:$Field,G}
                adder(a,b,$(QuoteNode(ADD)),$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
            @generated function $op(a::Simplex{V,G,A,S} where A,b::MultiVector{V,T}) where {V,T<:$Field,G,S<:$Field}
                adder(a,b,$(QuoteNode(ADD)),$(QuoteNode(bop)),$(QuoteNode(VEC)))
            end
        end
    end
    @eval begin
        +(b::Chain{V,G,T},a::SubManifold{V,G}) where {V,G,T<:$Field} = a+b
        +(b::Chain{V,G,T},a::SubManifold{V,L}) where {V,G,T<:$Field,L} = a+b
        +(b::Chain{V,G,T},a::Simplex{V,G,B,S} where B) where {V,G,T<:$Field,S<:$Field} = a+b
        +(b::Chain{V,G,T},a::Simplex{V,L,B,S} where B) where {V,G,T<:$Field,L,S<:$Field} = a+b
        +(b::MultiVector{V,T},a::SubManifold{V,G}) where {V,T<:$Field,G} = a+b
        +(b::MultiVector{V,T},a::Simplex{V,G,B,S} where B) where {V,T<:$Field,G,S<:$Field} = a+b
        @generated function -(b::Chain{V,G,T},a::SubManifold{V,G}) where {V,G,T<:$Field}
            adder(a,b,$(QuoteNode(SUB)),$(QuoteNode(ADD)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function -(b::Chain{V,G,T},a::SubManifold{V,L}) where {V,G,T<:$Field,L}
            adder(a,b,$(QuoteNode(SUB)),$(QuoteNode(ADD)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function -(b::Chain{V,G,T},a::Simplex{V,G,B,S} where B) where {V,G,T<:$Field,S<:$Field}
            adder(a,b,$(QuoteNode(SUB)),$(QuoteNode(ADD)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function -(b::Chain{V,G,T},a::Simplex{V,L,B,S} where B) where {V,G,T<:$Field,L,S<:$Field}
            adder(a,b,$(QuoteNode(SUB)),$(QuoteNode(ADD)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function -(b::MultiVector{V,T},a::SubManifold{V,G}) where {V,T<:$Field,G}
            adder(a,b,$(QuoteNode(SUB)),$(QuoteNode(ADD)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function -(b::MultiVector{V,T},a::Simplex{V,G,B,S} where B) where {V,T<:$Field,G,S<:$Field}
            adder(a,b,$(QuoteNode(SUB)),$(QuoteNode(ADD)),$(QuoteNode(VEC)),Val(true))
        end
    end
end

### Product Algebra Constructor

insert_t(x) = Expr(:block,:(t=promote_type(valuetype(a),valuetype(b))),x)

function generate_products(Field=Field,VEC=:mvec,MUL=:*,ADD=:+,SUB=:-,CONJ=:conj,PAR=false)
    TF = Field ∉ FieldsBig ? :Any : :T
    EF = Field ≠ Any ? Field : ExprField
    generate_sums(Field,VEC,MUL,ADD,SUB,CONJ,PAR)
    @eval begin
        @generated function *(a::Chain{V,G,T},b::Chain{V,L,S}) where {V,G,T<:$Field,L,S<:$Field}
            if G == 0
                return :(Chain{V,G}(broadcast($$MUL,Ref(a[1]),b.v)))
            elseif L == 0
                return :(Chain{V,G}(broadcast($$MUL,a.v,Ref(b[1]))))
            elseif G == mdims(V) && !istangent(V)
                return :(a[1]*complementlefthodge(~b))
            elseif L == mdims(V) && !istangent(V)
                return :(⋆(~a)*b[1])
            elseif binomial(mdims(V),G)*binomial(mdims(V),L)<(1<<cache_limit)
                $(insert_expr((:N,:t,:bnl,:ib,:μ),:svec)...)
                out = zeros(svec(N,t))
                B = indexbasis(N,L)
                for i ∈ 1:binomial(N,G)
                    @inbounds v,ibi = :(a[$i]),ib[i]
                    for j ∈ 1:bnl
                        @inbounds geomaddmulti!_pre(V,out,ibi,B[j],derive_pre(V,ibi,B[j],v,:(b[$j]),$(QuoteNode(MUL))))
                    end
                end
                return insert_t(:(MultiVector{V}($(Expr(:call,tvec(N,μ),out...)))))
            else return quote
                $(insert_expr((:N,:t,:bnl,:ib,:μ),$(QuoteNode(VEC)))...)
                out = zeros($$VEC(N,t))
                B = indexbasis(N,L)
                for i ∈ 1:binomial(N,G)
                    @inbounds v,ibi = a[i],ib[i]
                    v≠0 && for j ∈ 1:bnl
                        if @inbounds geomaddmulti!(V,out,ibi,B[j],derive_mul(V,ibi,B[j],v,b[j],$$MUL))&μ
                            $(insert_expr((:out,);mv=:out)...)
                            @inbounds geomaddmulti!(V,out,ibi,B[j],derive_mul(V,ibi,B[j],v,b[j],$$MUL))
                        end
                    end
                end
                return MultiVector{V}(out)
            end end
        end
        #=function *(a::Chain{V,1,T},b::Chain{W,1,S}) where {V,T<:$Field,W,S<:$Field}
            !(V == dual(W) && V ≠ W) && throw(error())
            $(insert_expr((:N,:t,:bnl,:ib),VEC)...)
            out = zeros($VEC(N,2,t))
            B = indexbasis(N,L)
            for i ∈ 1:binomial(N,G)
                for j ∈ 1:bnl
                    @inbounds geomaddmulti!(V,out,ib[i],B[j],$MUL(a[i],b[j]))
                end
            end
            return MultiVector{V}(out)
        end=#
        @generated function contraction(a::Chain{V,G,T},b::Chain{V,L,S}) where {V,G,L,T<:$Field,S<:$Field}
            G<L && (!istangent(V)) && (return g_zero(V))
            if binomial(mdims(V),G)*binomial(mdims(V),L)<(1<<cache_limit)
                $(insert_expr((:N,:t,:bng,:bnl),:svec)...)
                μ = istangent(V)|hasconformal(V)
                ia = indexbasis(N,G)
                ib = indexbasis(N,L)
                out = zeros(μ ? svec(N,Any) : svec(N,G-L,Any))
                for i ∈ 1:bng
                    @inbounds v,iai = :(a[$i]),ia[i]
                    for j ∈ 1:bnl
                        if μ
                            @inbounds skewaddmulti!_pre(V,out,iai,ib[j],derive_pre(V,iai,ib[j],v,:(b[$j]),$(QuoteNode(MUL))))
                        else
                            @inbounds skewaddblade!_pre(V,out,iai,ib[j],derive_pre(V,iai,ib[j],v,:(b[$j]),$(QuoteNode(MUL))))
                        end
                    end
                end
                return if μ
                    insert_t(:(MultiVector{$V}($(Expr(:call,istangent(V) ? tvec(N) : tvec(N,:t),out...)))))
                else
                    insert_t(:(value_diff(Chain{$V,G-L}($(Expr(:call,tvec(N,G-L,:t),out...))))))
                end
            else return quote
                $(insert_expr((:N,:t,:bng,:bnl,:μ),$(QuoteNode(VEC)))...)
                ia = indexbasis(N,G)
                ib = indexbasis(N,L)
                out = zeros(μ ? $$VEC(N,t) : $$VEC(N,G-L,t))
                for i ∈ 1:bng
                    @inbounds v,iai = a[i],ia[i]
                    v≠0 && for j ∈ 1:bnl
                        if μ
                            if @inbounds skewaddmulti!(V,out,iai,ib[j],derive_mul(V,iai,ib[j],v,b[j],$$MUL))
                                out,t = zeros(svec(N,Any)) .+ out,Any
                                @inbounds skewaddmulti!(V,out,iai,ib[j],derive_mul(V,iai,ib[j],v,b[j],$$MUL))
                            end
                        else
                            @inbounds skewaddblade!(V,out,iai,ib[j],derive_mul(V,iai,ib[j],v,b[j],$$MUL))
                        end
                    end
                end
                return μ ? MultiVector{V}(out) : value_diff(Chain{V,G-L}(out))
            end end
        end
        function *(a::Simplex{V,G,A,T} where {G,A},b::Simplex{V,L,B,S} where {L,B}) where {V,T<:$Field,S<:$Field}
            ba,bb = basis(a),basis(b)
            v = derive_mul(V,bits(ba),bits(bb),a.v,b.v,$MUL)
            Simplex(v,mul(ba,bb,v))
        end
        @generated function *(b::Chain{V,G,T},a::SubManifold{V,L}) where {V,G,L,T<:$Field}
            product(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function *(a::SubManifold{V,L},b::Chain{V,G,T}) where {V,G,L,T<:$Field}
            product(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)))
        end
        @generated function *(b::Chain{V,G,T},a::Simplex{V,L,B,S}) where {V,G,T<:$Field,L,B,S<:$Field}
            product(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function *(a::Simplex{V,L,B,S},b::Chain{V,G,T}) where {V,G,T<:$Field,L,B,S<:$Field}
            product(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)))
        end
        @generated function contraction(b::Chain{V,G,T},a::SubManifold{V,L}) where {V,G,T<:$Field,L}
            product_contraction(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function contraction(a::SubManifold{V,L},b::Chain{V,G,T}) where {V,G,T<:$Field,L}
            product_contraction(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)))
        end
        @generated function contraction(b::Chain{V,G,T},a::Simplex{V,L,B,S}) where {V,G,T<:$Field,B,S<:$Field,L}
            product_contraction(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)),Val(true))
        end
        @generated function contraction(a::Simplex{V,L,B,S},b::Chain{V,G,T}) where {V,G,T<:$Field,B,S<:$Field,L}
            product_contraction(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)))
        end
        ∧(a::$Field,b::$Field) = $MUL(a,b)
        ∧(a::F,b::B) where B<:TensorTerm{V,G} where {F<:$EF,V,G} = Simplex{V,G}(a,b)
        ∧(a::A,b::F) where A<:TensorTerm{V,G} where {F<:$EF,V,G} = Simplex{V,G}(b,a)
        #=∧(a::$Field,b::MultiGrade{V,G}) where V = MultiGrade{V,G}(a.*b.v)
        ∧(a::MultiGrade{V,G},b::$Field) where V = MultiGrade{V,G}(a.v.*b)=#
        #=∧(a::$Field,b::Chain{V,G,T}) where {V,G,T<:$Field} = Chain{V,G,T}(a.*b.v)
        ∧(a::Chain{V,G,T},b::$Field) where {V,G,T<:$Field} = Chain{V,G,T}(a.v.*b)
        ∧(a::$Field,b::MultiVector{V,T}) where {V,T<:$Field} = MultiVector{V,T}(a.*b.v)
        ∧(a::MultiVector{V,T},b::$Field) where {V,T<:$Field} = MultiVector{V,T}(a.v.*b)=#
    end
    for (op,po,GL,grass) ∈ ((:∧,:>,:(G+L),:exter),(:∨,:<,:(G+L-mdims(V)),:meet))
        grassaddmulti! = Symbol(grass,:addmulti!)
        grassaddblade! = Symbol(grass,:addblade!)
        grassaddmulti!_pre = Symbol(grassaddmulti!,:_pre)
        grassaddblade!_pre = Symbol(grassaddblade!,:_pre)
        prop = Symbol(:product_,op)
        @eval begin
            @generated function $op(a::Chain{w,G,T},b::Chain{W,L,S}) where {T<:$Field,w,S<:$Field,W,G,L}
                V = w==W ? w : ((w==dual(W)) ? (dyadmode(w)≠0 ? W⊕w : w⊕W) : (return :(interop($$op,a,b))))
                $po(G+L,mdims(V)) && (!istangent(V)) && (return g_zero(V))
                if binomial(mdims(w),G)*binomial(mdims(W),L)<(1<<cache_limit)
                    $(insert_expr((:N,:t,:μ),VEC,:T,:S)...)
                    ia = indexbasis(mdims(w),G)
                    ib = indexbasis(mdims(W),L)
                    out = zeros(μ ? svec(N,Any) : svec(N,$GL,Any))
                    CA,CB = isdual(w),isdual(W)
                    for i ∈ 1:binomial(mdims(w),G)
                        @inbounds v,iai = :(a[$i]),ia[i]
                        x = CA ? dual(V,iai) : iai
                        for j ∈ 1:binomial(mdims(W),L)
                            X = @inbounds CB ? dual(V,ib[j]) : ib[j]
                            if μ
                                $grassaddmulti!_pre(V,out,x,X,derive_pre(V,x,X,v,:(b[$j]),$(QuoteNode(MUL))))
                            else
                                $grassaddblade!_pre(V,out,x,X,derive_pre(V,x,X,v,:(b[$j]),$(QuoteNode(MUL))))
                            end
                        end
                    end
                    return if μ
                        insert_t(:(MultiVector{$V}($(Expr(:call,tvec(N),out...)))))
                    else
                        insert_t(:(Chain{$V,$$GL}($(Expr(:call,tvec(N,$GL,:t),out...)))))
                    end
                else return quote
                    $(insert_expr((:N,:t,:μ),$(QuoteNode(VEC)))...)
                    ia = indexbasis(mdims(w),G)
                    ib = indexbasis(mdims(W),L)
                    out = zeros(μ $$VEC(N,t) : $$VEC(N,$$GL,t))
                    CA,CB = isdual(w),isdual(W)
                    for i ∈ 1:binomial(mdims(w),G)
                        @inbounds v,iai = a[i],ia[i]
                        x = CA ? dual(V,iai) : iai
                        v≠0 && for j ∈ 1:binomial(mdims(W),L)
                            X = @inbounds CB ? dual(V,ib[j]) : ib[j]
                            if μ
                                if @inbounds $$grassaddmulti!(V,out,x,X,derive_mul(V,x,X,v,b[j],$$MUL))
                                    out,t = zeros(svec(N,promote_type,Any)) .+ out,Any
                                    @inbounds $$grassaddmulti!(V,out,x,X,derive_mul(V,x,X,v,b[j],$$MUL))
                                end
                            else
                                @inbounds $$grassaddblade!(V,out,x,X,derive_mul(V,x,X,v,b[j],$$MUL))
                            end
                        end
                    end
                    return μ ? MultiVector{V}(out) : Chain{V,$$GL}(out)
                end end
            end
            @generated function $op(b::Chain{Q,G,T},a::SubManifold{R,L}) where {Q,G,T<:$Field,R,L}
                $prop(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)),Val(true))
            end
            @generated function $op(a::SubManifold{Q,G},b::Chain{R,L,T}) where {Q,R,T<:$Field,G,L}
                $prop(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)))
            end
            @generated function $op(b::Chain{Q,G,T},a::Simplex{R,L,B,S}) where {Q,G,T<:$Field,R,B,S<:$Field,L}
                $prop(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)),Val(true))
            end
            @generated function $op(a::Simplex{Q,G,B,S},b::Chain{R,L,T}) where {T<:$Field,Q,R,B,S<:$Field,G,L}
                $prop(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)))
            end
        end
    end
    for (op,product!) ∈ ((:∧,:exteraddmulti!),(:*,:geomaddmulti!),
                         (:∨,:meetaddmulti!),(:contraction,:skewaddmulti!))
        preproduct! = Symbol(product!,:_pre)
        prop = op≠:* ? Symbol(:product_,op) : :product
        @eval begin
            @generated function $op(a::MultiVector{V,T},b::Chain{V,G,S}) where {V,T<:$Field,S<:$Field,G}
                if binomial(mdims(V),G)*(1<<mdims(V))<(1<<cache_limit)
                    $(insert_expr((:N,:t,:out,:bng,:ib,:bs,:bn,:μ),:svec)...)
                    for g ∈ 1:N+1
                        A = indexbasis(N,g-1)
                        @inbounds for i ∈ 1:bn[g]
                            @inbounds val = :(a.v[$(bs[g]+i)])
                            for j ∈ 1:bng
                                @inbounds $preproduct!(V,out,A[i],ib[j],derive_pre(V,A[i],ib[j],val,:(b[$j]),$(QuoteNode(MUL))))
                            end
                        end
                    end
                    return insert_t(:(MultiVector{V}($(Expr(:call,tvec(N,μ),out...)))))
                else return quote
                    $(insert_expr((:N,:t,:out,:bng,:ib,:bs,:bn,:μ),$(QuoteNode(VEC)))...)
                    for g ∈ 1:N+1
                        A = indexbasis(N,g-1)
                        @inbounds for i ∈ 1:bn[g]
                            @inbounds val = a.v[bs[g]+i]
                            val≠0 && for j ∈ 1:bng
                                if @inbounds $$product!(V,out,A[i],ib[j],derive_mul(V,A[i],ib[j],val,b[j],$$MUL))&μ
                                    $(insert_expr((:out,);mv=:out)...)
                                    @inbounds $$product!(V,out,A[i],ib[j],derive_mul(V,A[i],ib[j],val,b[j],$$MUL))
                                end
                            end
                        end
                    end
                    return MultiVector{V}(out)
                end end
            end
            @generated function $op(a::Chain{V,G,T},b::MultiVector{V,S}) where {V,G,S<:$Field,T<:$Field}
                if binomial(mdims(V),G)*(1<<mdims(V))<(1<<cache_limit)
                    $(insert_expr((:N,:t,:out,:bng,:ib,:bs,:bn,:μ),:svec)...)
                    for g ∈ 1:N+1
                        B = indexbasis(N,g-1)
                        @inbounds for i ∈ 1:bn[g]
                            @inbounds val = :(b.v[$(bs[g]+i)])
                            for j ∈ 1:bng
                                @inbounds $preproduct!(V,out,ib[j],B[i],derive_pre(V,ib[j],B[i],:(a[$j]),val,$(QuoteNode(MUL))))
                            end
                        end
                    end
                    return insert_t(:(MultiVector{V}($(Expr(:call,tvec(N,μ),out...)))))
                else return quote
                    $(insert_expr((:N,:t,:out,:bng,:ib,:bs,:bn,:μ),$(QuoteNode(VEC)))...)
                    for g ∈ 1:N+1
                        B = indexbasis(N,g-1)
                        @inbounds for i ∈ 1:bn[g]
                            @inbounds val = b.v[bs[g]+i]
                            val≠0 && for j ∈ 1:bng
                                if @inbounds $$product!(V,out,ib[j],B[i],derive_mul(V,ib[j],B[i],a[j],val,$$MUL))&μ
                                    $(insert_expr((:out,);mv=:out)...)
                                    @inbounds $$product!(V,out,ib[j],B[i],derive_mul(V,ib[j],B[i],a[j],val,$$MUL))
                                end
                            end
                        end
                    end
                    return MultiVector{V}(out)
                end end
            end
            @generated function $op(a::MultiVector{V,T},b::MultiVector{V,S}) where {V,T<:$Field,S<:$Field}
                loop = generate_loop_multivector(V,:(a.v),:(b.v),$(QuoteNode(MUL)),$product!,$preproduct!)
                if mdims(V)<cache_limit/2
                    return insert_t(:(MultiVector{V}($(loop[2].args[2]))))
                else return quote
                    $(insert_expr(loop[1],$(QuoteNode(VEC)))...)
                    $(loop[2])
                    return MultiVector{V,t}(out)
                end end
            end
            @generated function $op(b::MultiVector{V,T},a::SubManifold{V,G,B}) where {V,T<:$Field,G,B}
                $prop(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)),Val(true))
            end
            @generated function $op(a::SubManifold{V,G,A},b::MultiVector{V,T}) where {V,G,A,T<:$Field}
                $prop(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)))
            end
            @generated function $op(b::MultiVector{V,T},a::Simplex{V,G,B,S}) where {V,T<:$Field,G,B,S<:$Field}
                $prop(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)),Val(true))
            end
            @generated function $op(a::Simplex{V,G,B,T},b::MultiVector{V,S}) where {V,G,B,T<:$Field,S<:$Field}
                $prop(a,b,$(QuoteNode(MUL)),$(QuoteNode(VEC)))
            end
        end
    end
    for side ∈ (:left,:right)
        c,p = Symbol(:complement,side),Symbol(:parity,side)
        h,pg,pn = Symbol(c,:hodge),Symbol(p,:hodge),Symbol(p,:null)
        pnp = :(Leibniz.$(Symbol(pn,:pre)))
        for (c,p) ∈ ((c,p),(h,pg))
            @eval begin
                @generated function $c(b::Chain{V,G,T}) where {V,G,T<:$Field}
                    isdyadic(V) && throw(error("Complement for dyadic tensors is undefined"))
                    if binomial(mdims(V),G)<(1<<cache_limit)
                        $(insert_expr((:N,:ib,:D),:svec)...)
                        P = $(c≠h ? 0 : :(hasinf(V)+hasorigin(V)))
                        out = zeros(svec(N,G,Any))
                        D = diffvars(V)
                        for k ∈ 1:binomial(N,G)
                            val = :(b.v[$k])
                            @inbounds p = $p(V,ib[k])
                            v = $(c≠h ? :($pnp(V,ib[k],val)) : :val)
                            v = typeof(V)<:Signature ? (p ? :($$SUB($v)) : v) : Expr(:call,$MUL,p,v)
                            @inbounds setblade!_pre(out,v,complement(N,ib[k],D,P),Val{N}())
                        end
                        return :(Chain{V,$(N-G)}($(Expr(:call,tvec(N,N-G,:T),out...))))
                    else return quote
                        $(insert_expr((:N,:ib,:D),$(QuoteNode(VEC)))...)
                        P = $(c≠h ? 0 : :(hasinf(V)+hasorigin(V)))
                        out = zeros($$VEC(N,G,T))
                        D = diffvars(V)
                        for k ∈ 1:binomial(N,G)
                            @inbounds val = b.v[k]
                            if val≠0
                                @inbounds p = $$p(V,ib[k])
                                v = $(c≠h ? :($$pn(V,ib[k],val)) : :val)
                                v = typeof(V)<:Signature ? (p ? $$SUB(v) : v) : $$MUL(p,v)
                                @inbounds setblade!(out,v,complement(N,ib[k],D,P),Val{N}())
                            end
                        end
                        return Chain{V,N-G}(out)
                    end end
                end
                @generated function $c(m::MultiVector{V,T}) where {V,T<:$Field}
                    isdyadic(V) && throw(error("Complement for dyadic tensors is undefined"))
                    if mdims(V)<cache_limit
                        $(insert_expr((:N,:bs,:bn),:svec)...)
                        P = $(c≠h ? 0 : :(hasinf(V)+hasorigin(V)))
                        out = zeros(svec(N,Any))
                        D = diffvars(V)
                        for g ∈ 1:N+1
                            ib = indexbasis(N,g-1)
                            @inbounds for i ∈ 1:bn[g]
                                val = :(m.v[$(bs[g]+i)])
                                v = $(c≠h ? :($pnp(V,ib[i],val)) : :val)
                                v = typeof(V)<:Signature ? ($p(V,ib[i]) ? :($$SUB($v)) : v) : Expr(:call,:*,$p(V,ib[i]),v)
                                @inbounds setmulti!_pre(out,v,complement(N,ib[i],D,P),Val{N}())
                            end
                        end
                        return :(MultiVector{V}($(Expr(:call,tvec(N,:T),out...))))
                    else return quote
                        $(insert_expr((:N,:bs,:bn),$(QuoteNode(VEC)))...)
                        P = $(c≠h ? 0 : :(hasinf(V)+hasorigin(V)))
                        out = zeros($$VEC(N,T))
                        D = diffvars(V)
                        for g ∈ 1:N+1
                            ib = indexbasis(N,g-1)
                            @inbounds for i ∈ 1:bn[g]
                                @inbounds val = m.v[bs[g]+i]
                                if val≠0
                                    v = $(c≠h ? :($$pn(V,ib[i],val)) : :val)
                                    v = typeof(V)<:Signature ? ($$p(V,ib[i]) ? $$SUB(v) : v) : $$p(V,ib[i])*v
                                    @inbounds setmulti!(out,v,complement(N,ib[i],D,P),Val{N}())
                                end
                            end
                        end
                        return MultiVector{V}(out)
                    end end
                end
            end
        end
    end
    for reverse ∈ (:reverse,:involute,:conj,:clifford)
        p = Symbol(:parity,reverse)
        @eval begin
            @generated function $reverse(b::Chain{V,G,T}) where {V,G,T<:$Field}
                if binomial(mdims(V),G)<(1<<cache_limit)
                    D = diffvars(V)
                    D==0 && !$p(G) && (return :b)
                    $(insert_expr((:N,:ib),:svec)...)
                    out = zeros(svec(N,G,Any))
                    for k ∈ 1:binomial(N,G)
                        @inbounds v = :(b.v[$k])
                        if D==0
                            @inbounds setblade!_pre(out,:($$SUB($v)),ib[k],Val{N}())
                        else
                            @inbounds B = ib[k]
                            setblade!_pre(out,$p(grade(V,B)) ? :($$SUB($v)) : v,B,Val{N}())
                        end
                    end
                    return :(Chain{V,G}($(Expr(:call,tvec(N,G,:T),out...))))
                else return quote
                    D = diffvars(V)
                    D==0 && !$$p(G) && (return b)
                    $(insert_expr((:N,:ib),$(QuoteNode(VEC)))...)
                    out = zeros($$VEC(N,G,T))
                    for k ∈ 1:binomial(N,G)
                        @inbounds v = b.v[k]
                        v≠0 && if D==0
                            @inbounds setblade!(out,$$SUB(v),ib[k],Val{N}())
                        else
                            @inbounds B = ib[k]
                            setblade!(out,$$p(grade(V,B)) ? $$SUB(v) : v,B,Val{N}())
                        end
                    end
                    return Chain{V,G}(out)
                end end
            end
            @generated function $reverse(m::MultiVector{V,T}) where {V,T<:$Field}
                if mdims(V)<cache_limit
                    $(insert_expr((:N,:bs,:bn,:D),:svec)...)
                    out = zeros(svec(N,Any))
                    for g ∈ 1:N+1
                        pg = $p(g-1)
                        ib = indexbasis(N,g-1)
                        @inbounds for i ∈ 1:bn[g]
                            @inbounds v = :(m.v[$(bs[g]+i)])
                            if D==0
                                @inbounds setmulti!(out,pg ? :($$SUB($v)) : v,ib[i],Val{N}())
                            else
                                @inbounds B = ib[i]
                                setmulti!(out,$p(grade(V,B)) ? :($$SUB($v)) : v,B,Val{N}())
                            end
                        end
                    end
                    return :(MultiVector{V}($(Expr(:call,tvec(N,:T),out...))))
                else return quote
                    $(insert_expr((:N,:bs,:bn,:D),$(QuoteNode(VEC)))...)
                    out = zeros($$VEC(N,T))
                    for g ∈ 1:N+1
                        pg = $$p(g-1)
                        ib = indexbasis(N,g-1)
                        @inbounds for i ∈ 1:bn[g]
                            @inbounds v = m.v[bs[g]+i]
                            v≠0 && if D==0
                                @inbounds setmulti!(out,pg ? $$SUB(v) : v,ib[i],Val{N}())
                            else
                                @inbounds B = ib[i]
                                setmulti!(out,$$p(grade(V,B)) ? $$SUB(v) : v,B,Val{N}())
                            end
                        end
                    end
                    return MultiVector{V}(out)
                end end
            end
        end
    end
end
