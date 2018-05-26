signature BIGNAT =      (*  Given Signature  *)
sig
type bignat
exception overflow
exception underflow
val zero : bignat
val normalize : bignat -> bignat
val fromString : string -> bignat
val toString : bignat -> string
val ++ : bignat * bignat -> bignat
val succ : bignat -> bignat
val min : bignat * bignat -> bignat
val max : bignat * bignat -> bignat
val ** : bignat * bignat -> bignat
val compare : bignat * bignat -> order
val << : bignat * bignat -> bool
val <<= : bignat * bignat -> bool
val >> : bignat * bignat -> bool
val >>= : bignat * bignat -> bool
val == : bignat * bignat -> bool
val len : bignat -> int
val lenCompare : bignat * bignat -> order
val lenLt : bignat * bignat -> bool
val lenLeq : bignat * bignat -> bool
val lenGt : bignat * bignat -> bool
val lenGeq : bignat * bignat -> bool
val lenEq : bignat * bignat -> bool
val -- : bignat * bignat -> bignat
val pred : bignat -> bignat
exception division_by_zero
exception emptyList
val %% : bignat * bignat -> bignat * bignat
val quo : bignat * bignat -> bignat
val rem : bignat * bignat -> bignat
end

structure Bignat: BIGNAT =          (*  Structure Defined   *)
struct
    type bignat = int list

    exception overflow;
    exception underflow;
    exception division_by_zero;
    exception emptyList;

    val zero = [0]

    fun normalize([]) = raise emptyList
        | normalize(L) = if(length(L)=1 andalso hd(L)=0) then L
                        else if(hd(L) = 0) then normalize(tl(L))
                        else L

    fun fromString("") = raise underflow
        | fromString(x) =
        let
            fun ctoi([]) = []
            | ctoi(h::t) = (ord(h)-48)::ctoi(t)
        in  normalize(ctoi(explode(x)))
        end;

    fun toString([]) = raise emptyList
        | toString(L) = 
        let 
            fun itoc([]) = []
            | itoc(h::t) = (chr(h+48))::itoc(t)
        in implode(itoc(L))
        end;


    infix ++;
    fun p ++ q =
        let
            fun addList([], [], carry) = [carry]
                | addList([], h::t, carry) = ((h+carry) mod 10)::addList([], t, ((h+carry) div 10))
                | addList(h::t, [], carry) =  ((h+carry) mod 10)::addList([], t, ((h+carry) div 10))
                | addList(h1::t1, h2::t2, carry) =  ((h1+h2+carry) mod 10)::addList(t1, t2, ((h1+h2+carry) div 10))
        in
            normalize(rev(addList(rev(normalize(p)),rev(normalize(q)),0)))
        end;infix ++;

    infix ==;
    fun p == q =
        let
            fun equal([],[])=true
                |equal([],L)=false
                | equal(L,[])=false
                | equal(h1::t1, h2::t2) = if(h1=h2) then equal(t1, t2)
                                            else false
        in
            equal(normalize(p),normalize(q))
        end;
    
    infix <<;
    fun p << q =
        let
            fun lt([],[])=false
                | lt([],L)=true
                | lt(L,[])=false
                | lt(L1, L2) = if(length(L1)<length(L2)) then true
                                else if(length(L1)>length(L2)) then false
                                else if(hd(L1)=hd(L2)) then lt(tl(L1),tl(L2))
                                else if(hd(L1)<hd(L2)) then true
                                else if(hd(L1)>hd(L2)) then false
                                else false
        in
            lt(normalize(p),normalize(q))
        end;

    infix <<=;
    fun p <<= q =
        let
            fun lt([],[])=true
                | lt([],L)=true
                | lt(L,[])=false
                | lt(L1, L2) = if(length(L1)<length(L2)) then true
                                else if(length(L1)>length(L2)) then false
                                else if(hd(L1)=hd(L2)) then lt(tl(L1),tl(L2))
                                else if(hd(L1)<hd(L2)) then true
                                else if(hd(L1)>hd(L2)) then false
                                else false
        in
            lt(normalize(p),normalize(q))
        end;

    infix >>;
    fun p >> q =
        let
            fun lt([],[])=false
                | lt([],L)=false
                | lt(L,[])=true
                | lt(L1, L2) = if(length(L1)<length(L2)) then false
                                else if(length(L1)>length(L2)) then true
                                else if(hd(L1)=hd(L2)) then lt(tl(L1),tl(L2))
                                else if(hd(L1)<hd(L2)) then false
                                else if(hd(L1)>hd(L2)) then true
                                else false
        in
            lt(normalize(p),normalize(q))
        end;

    infix >>=;
    fun p >>= q =
        let
            fun lt([],[])=true
                | lt([],L)=false
                | lt(L,[])=true
                | lt(L1, L2) = if(length(L1)<length(L2)) then false
                                else if(length(L1)>length(L2)) then true
                                else if(hd(L1)=hd(L2)) then lt(tl(L1),tl(L2))
                                else if(hd(L1)<hd(L2)) then false
                                else if(hd(L1)>hd(L2)) then true
                                else false
        in
            lt(normalize(p),normalize(q))
        end;
    fun compare(L1,L2)=if(L1<<L2) then LESS
                        else if(L1==L2) then EQUAL
                        else GREATER

    fun len(L1)=length(normalize(L1))
    fun lenLt(L1,L2)=length(normalize(L1))<length(normalize(L2))
    fun lenLeq(L1,L2)=length(normalize(L1))<=length(normalize(L2))
    fun lenGt(L1,L2)=length(normalize(L1))>length(normalize(L2))
    fun lenGeq(L1,L2)=length(normalize(L1))>=length(normalize(L2))
    fun lenEq(L1,L2)=length(normalize(L1))=length(normalize(L2))
    fun lenCompare(L1,L2)=if(lenLt(L1,L2)) then LESS
                            else if(lenEq(L1,L2)) then EQUAL
                            else GREATER

    infix --;
    fun p -- q =
        let
            fun subList([], [], borrow) = []
                | subList([], L, borrow) = []
                | subList(h::t, [], borrow) =   if(borrow=0) then 
                                                    h::t
                                                else
                                                    if(h-1>=0) then ((h-1)::subList(t, [], 0))
                                                    else ((10+(h-1)-0)::subList(t, [], 1))
                | subList(h1::t1, h2::t2, borrow) = if(borrow=0) then
                                                        if(h1>=h2) then ((h1-h2)::subList(t1, t2, 0))
                                                        else ((10+h1-h2)::subList(t1, t2, 1))
                                                    else
                                                        if(h1-1>=h2) then ((h1-1-h2)::subList(t1, t2, 0))
                                                        else ((10+(h1-1)-h2)::subList(t1, t2, 1))
        in
            if(p<<q) then raise underflow
            else if(p==q) then [0]
            else normalize(rev(subList(rev(normalize(p)),rev(normalize(q)),0)))
        end;

    infix **;
    fun p ** q =
        let
            fun mulList2([],x,carry) = [carry]
                | mulList2(h::t,x,carry) = ((h*x+carry) mod 10)::mulList2(t, x, (h*x+carry) div 10)
            fun shift(L,va) = if(va=0) then L
                                else 0::shift(L,va-1)
            fun mulList1(L,[],count, ans)= ans
                | mulList1(L ,h::t, count, ans)= mulList1(L, t, count+1,ans ++ rev(shift(mulList2(L,h,0), count)))
        in
            normalize(mulList1(rev(normalize(p)),rev(normalize(q)),0,[0]))
        end;
    
    infix %%;
    fun p %% q =
        let
            fun comp(L1,L2,i)=  if(L1==(L2**i)) then (i,[0])
                                else if(L1>>(L2**i)) then comp(L1, L2, i++[1])
                                else (i--[1],L1--(L2**(i--[1])))
            fun div1(L1,L2)=if(L1<<L2) then ([0],L1)
                            else comp(L1,L2,[1])
            fun divList([],p,rem,q)=(q,rem)
                | divList(h::t,p,rem,q)=
                    let
                        val temp = div1(rem@[h],p);
                    in
                        divList(t,p,normalize(#2temp),normalize(q@(#1temp))) 
                    end;
        in
            if(length(normalize(q))=1 andalso hd(normalize(q))=0) then raise division_by_zero
            else divList(normalize(p),normalize(q),[],[])
        end;
    fun quo(p,q) = #1(p %% q)
    fun rem(p,q) = #2(p %% q)

    fun succ(L) = L ++ [1]

    fun pred(L) = L -- [1]

    fun min(L1, L2) = if(L1 <<= L2) then L1
                        else L2

    fun max(L1, L2) = if(L1 >>= L2) then L1
                        else L2
end;
infix %%;
infix ++;
infix --;
infix **;
infix <<;
infix <<=;
infix >>;
infix >>=;
infix ==;
(* open Bignat; *)
