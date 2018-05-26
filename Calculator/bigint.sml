use "bignat.sml";
functor BigInt (Bn:BIGNAT):                   (*  Given Signature *)
    sig
    type bigint
    val bigzero: bigint
    val normalize : bigint -> bigint
    val bigint: int -> bigint
    val fromString : string -> bigint
    val toString : bigint -> string
    val int : bigint -> int option
    val ~~ : bigint -> bigint
    val abs : bigint -> bigint
    val ++ : bigint * bigint -> bigint
    val succ : bigint -> bigint
    val min : bigint * bigint -> bigint
    val max : bigint * bigint -> bigint
    val sign : bigint -> int
    val sameSign : bigint * bigint -> bool
    val ** : bigint * bigint -> bigint
    val compare : bigint * bigint -> order
    val << : bigint * bigint -> bool
    val <<= : bigint * bigint -> bool
    val >> : bigint * bigint -> bool
    val >>= : bigint * bigint -> bool
    val == : bigint * bigint -> bool
    val len : bigint -> int
    val lenCompare : bigint * bigint -> order
    val lenLt : bigint * bigint -> bool
    val lenLeq : bigint * bigint -> bool
    val lenGt : bigint * bigint -> bool
    val lenGeq : bigint * bigint -> bool
    val lenEq : bigint * bigint -> bool
    val -- : bigint * bigint -> bigint
    val pred : bigint -> bigint
    exception division_by_zero
    val %% : bigint * bigint -> bigint * bigint
    val quo : bigint * bigint -> bigint
    val rem : bigint * bigint -> bigint 
    end (* sig *)=
struct                                                   (*  Given Structure  *)
    type bigint = Bn.bignat * int

    exception division_by_zero;

    val bigzero = (Bn.zero,0)

    fun normalize(N:bigint) = (Bn.normalize(#1N),#2N) 

    fun fromString(S) = if(ord(String.sub(S,0))=126) then (Bn.fromString(implode(tl(explode(S)))),1)
                        else (Bn.fromString(S),0)

    fun toString(N:bigint) = if(#2N=1) then "~"^Bn.toString(#1N)
                        else Bn.toString(#1N)

    fun ~~ (p:bigint) = if(#2p=0) then (#1p,1)
                else (#1p,0)

    fun abs(N:bigint) = (#1N,0)

    fun sameSign(p:bigint,q:bigint) = if((#2p) = (#2q)) then true
                                        else false

    infix >>;
    fun (p:bigint) >> (q:bigint) = if(#2p=1 andalso #2q=0) then false
                                    else if(#2p=0 andalso #2q=1) then true
                                    else if(#2p=1 andalso #2q=1) then  Bn.<<(#1p,#1q) 
                                    else Bn.>>(#1p,#1q) 
    infix >>=;
    fun (p:bigint) >>= (q:bigint) = if(#2p=1 andalso #2q=0) then false
                                    else if(#2p=0 andalso #2q=1) then true
                                    else if(#2p=1 andalso #2q=1) then Bn.<<=(#1p,#1q) 
                                    else  Bn.>>=(#1p,#1q) 

    infix <<;
    fun (p:bigint) << (q:bigint) = if(#2p=1 andalso #2q=0) then true
                                    else if(#2p=0 andalso #2q=1) then false
                                    else if(#2p=1 andalso #2q=1) then Bn.>>(#1p,#1q) 
                                    else  Bn.<<(#1p,#1q) 

    infix <<=;
    fun (p:bigint) <<= (q:bigint) = if(#2p=1 andalso #2q=0) then true
                                    else if(#2p=0 andalso #2q=1) then false
                                    else if(#2p=1 andalso #2q=1) then Bn.>>=(#1p,#1q) 
                                    else  Bn.<<=(#1p,#1q) 

    infix ==;
    fun (p:bigint) == (q:bigint) = if(sameSign(p,q) andalso Bn.==(#1p,#1q) ) then true
                                    else false

    infix ++;
    fun (p:bigint) ++ (q:bigint) = if(sameSign(p,q)) then (Bn.++(#1p,#1q) , #2p)
                                    else if(#2p=0 andalso #2q=1) then
                                            if(Bn.>>=(#1p,#1q)) then (Bn.--(#1p,#1q) , 0)
                                            else (Bn.--(#1q,#1p) , 1)
                                    else if(Bn.>>=(#1p,#1q)) then (Bn.--(#1p,#1q) , 1)
                                            else (Bn.--(#1q,#1p) , 0)

    infix --;
    fun (p:bigint) -- (q:bigint) = if((#2p=0 andalso #2q=1) orelse (#2p=1 andalso #2q=0)) then (Bn.++(#1p,#1q), #2p)
                                    else if(#2p=0 andalso #2q=0) then
                                            if(Bn.>>=(#1p,#1q)) then (Bn.--(#1p,#1q) , 0)
                                            else (Bn.--(#1q,#1p) , 1)
                                    else if(Bn.>>=(#1p,#1q)) then (Bn.--(#1p,#1q) , 1)
                                            else (Bn.--(#1q,#1p) , 0)
    
    infix **;
    fun (p:bigint) ** (q:bigint) = if(sameSign(p,q)) then (Bn.**(#1q,#1p),0)
                                    else (Bn.**(#1q,#1p),1)

    fun succ(p:bigint) = p ++ (Bn.fromString("1"),0)

    fun pred(p:bigint) = p ++ (Bn.fromString("1"),1)

    fun min(p:bigint,q:bigint) = if(p <<= q ) then p
                                    else q

    fun max(p:bigint,q:bigint) = if(p >>= q ) then p
                                    else q
    
    fun sign(p:bigint) = #2p

    fun len(p:bigint) = Bn.len(#1p)

    fun lenLt(p:bigint,q:bigint) = Bn.lenLt(#1p,#1q)

    fun lenLeq(p:bigint,q:bigint) = Bn.lenLeq(#1p,#1q)

    fun lenGt(p:bigint,q:bigint) = Bn.lenGt(#1p,#1q)

    fun lenGeq(p:bigint,q:bigint) = Bn.lenGeq(#1p,#1q)

    fun lenEq(p:bigint,q:bigint) = Bn.lenEq(#1p,#1q)   

    fun compare(L1:bigint,L2:bigint)=if(L1<<L2) then LESS
                                        else if(L1==L2) then EQUAL
                                        else GREATER

    fun lenCompare(L1:bigint,L2:bigint)=if(lenLt(L1,L2)) then LESS
                                        else if(lenEq(L1,L2)) then EQUAL
                                        else GREATER

    fun bigint(p) = fromString(Int.toString(p))

    fun int(p:bigint) = Int.fromString(toString(p))

    infix %%;
    fun (p:bigint) %% (q:bigint) = 
                                let
                                  val temp=Bn.%%(#1p,#1q);
                                in
                                  if(sameSign(p,q)) then ((#1temp,0),(#2temp,0))
                                  else if(Bn.==(#2temp,Bn.zero)) then ((#1temp,1),(#2temp,0))
                                  else ((Bn.++(#1temp,Bn.fromString("1")),1),(Bn.--(#1q,#2temp),0))
                                end

    fun quo(p:bigint,q:bigint) = #1(p%%q)
    fun rem(p:bigint,q:bigint) = #2(p%%q)
    
 
end;

