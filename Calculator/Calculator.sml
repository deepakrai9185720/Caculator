use "bigint.sml" ;
structure ob = BigInt(Bignat);
open ob;
fun isNumber([]) = 1
      |isNumber(a:int list) =
          if(hd(a) > ~1)
             then  if(hd(a) < 10)
                      then isNumber(tl(a))
                   else
                       0
          else
              0

(***************************************************************************************************************)              

fun isLeftParantheses(p:int) =
        if (p = ~8 ) 
           then 1
        else 0;


(***************************************************************************************************************)              

fun isRightParantheses(p:int) =
        if (p = ~7 ) 
           then 1
        else 0;


(***************************************************************************************************************)              

fun isOperator(p:int)=
        if (p = ~1 orelse p = ~3 orelse p = ~5 orelse p = ~6) 
          then p
       else 
           0;

(***************************************************************************************************************)              

fun toBig(li:char list)=
        case li of
        []=>[]
       |x::xs=>(Char.ord(x)-48)::toBig(xs);

(***************************************************************************************************************)

fun f (a:string) =
               let val lis=explode a
               in toBig(lis)
               end

(***************************************************************************************************************)

fun isDigit(a:int) =
    if(a > ~1 )
      then if(a<=9)
         then true
        else
          false
    else
      false   

(***************************************************************************************************************)

fun isNotDigit(a:int) =
    if(a > ~1 )
      then if(a<9)
         then false
        else
          true
    else
      true       

(***************************************************************************************************************)

fun isMDGRoup([]) = 1
     |isMDGRoup(a:int list) =
         if( isNotDigit(hd(a)) andalso hd(a)<> ~1 andalso  hd(a)<> ~6) 
           then 0
         else
            isMDGRoup(tl(a))

(***************************************************************************************************************)

fun checker([]) = []
     | checker(a:int list) = 
        if(hd(a) = ~1 orelse hd(a) = ~6 )
           then []
        else
           hd(a)::checker(tl(a))  

(***************************************************************************************************************)
 
 fun checker2([],leftParantheses,rightParantheses) = []
      | checker2(p:int list,leftParantheses,rightParantheses) =
         if (isLeftParantheses(hd(p)) = 1) 
                 then hd(p)::checker2(tl(p),leftParantheses+1,rightParantheses)
          else if(isRightParantheses(hd(p)) = 1)
                then if(leftParantheses = rightParantheses+1)
                      then []
                     else
                        hd(p)::checker2(tl(p),leftParantheses,rightParantheses+1)        
          else
               hd(p)::checker2(tl(p),leftParantheses,rightParantheses)               

(***************************************************************************************************************)     

fun checker3([])=[]
   |  checker3(p:int list) =
      if(isDigit(hd(p)))
          then hd(p)::checker3(tl(p))
       else 
            []  

(***************************************************************************************************************)     
 
fun leftoperand([])=[] 
    | leftoperand(p:int list) =
        if(isMDGRoup(p)=1) 
          then  checker(p)
        else if(isLeftParantheses(hd(p))=1)
           then checker2(tl(p),1,0)
        else 
           checker3(p)

(***************************************************************************************************************)     
            
fun operand([],a)= ~4
     |operand(p:int list,a) =
      if(a=0)  
        then if(isOperator(hd(p))<>0)
               then hd(p)
             else 
                operand(tl(p),a)  
          
      else 
        operand(tl(p),a-1)   


(***************************************************************************************************************)     

fun operand2(p:int list,a,i,j) =
      if(j = ~4)
         then ~1
      else if(a=0)  
         then if(isOperator(hd(p))<>0)
                then i+1
              else 
                 operand2(tl(p),a,i+1,j)  
          
      else 
        operand2(tl(p),a-1,i+1,j)   
        

(***************************************************************************************************************)     


fun rightoperand(xs, n) =
	if n < 0 then []
	else if n = 0 then xs
	else 
		case xs of 
			[] => []
		  | (_::xs') => rightoperand(xs', n-1)        

(***************************************************************************************************************)     


(***********************************************************************************************************************************************************************************)

fun fd [] = []
  | fd (x::xs) =  ~x::fd (xs);


(***********************************************************************************************************************************************************************************)

(***********************************************************************************************************************************************************************************)

fun perform(p:bigint, q:int ,r:bigint)=
       if(q= ~5)
           then  p ++ r
       else if(q= ~3)
           then p -- r
        else if(q= ~1)
            then quo(p,r) 
        else if(q= ~6)
           then p ** r
         else 
           raise Subscript      
           
                           

(***************************************************************************************************************)     

fun drop(xs, n) =
	if n < 0 then raise Subscript
	else if n = 0 then xs
	else 
		case xs of 
			[] => []
		  | (_::xs') => drop(xs', n-1)

(***************************************************************************************************************)

fun tostring([])=""
       | tostring(l)=
          let
              val aa=(l)
              fun toS([])=""
                 |toS(x::xs) =
                     if(isOperator(x) <> 0)
                         then if(x= ~1)
                                  then   "/" ^toS(xs) 
                              else if(x= ~5)
                                   then  "+" ^toS(xs)
                               else if(x= ~3)
                                  then "-" ^toS(xs)
                               else
                                  "*" ^toS(xs)
                     else if(x = ~7)
                          then ")" ^toS(xs)
                     else if(x = ~8)
                          then "(" ^toS(xs)
                     else 
                         Int.toString(x)^toS(xs)                      

           in toS(aa)
       end    


(***************************************************************************************************************)     
    
fun calc(p:int list):bigint=
     if(isNumber(p)=1)
        then fromString(tostring(p))
     else 
        let 
           val a=leftoperand(p)
           val b=operand(p,List.length(a))
           val c=operand2(p,List.length(a),0,b)
           val d=rightoperand(p,c)
        in            
         if(List.length(d) = 0)
             then calc(a)
         else 
             perform(calc(a),b,calc(d))     
        end     

(***************************************************************************************************************)     

fun zerogiver([],m,i) = []
    | zerogiver(l:int list,m,i) =
   if(hd(l) = ~3 )
       then if(i = 0)
            then [0]@[~3]@zerogiver(tl(l),hd(l),i+1)
           else 
              if(isDigit(m) = false andalso m <> ~7)
                 then [0]@[~3]@zerogiver(tl(l),hd(l),i+1)
              else 
                 [~3]@zerogiver(tl(l),hd(l),i+1)
   else 
       [hd(l)]@zerogiver(tl(l),hd(l),i+1)                 

(***************************************************************************************************************)

 fun take(n,[])=[]
     |take(n,x::xs)=
        if(n>0)
            then  x::take(n-1,xs)
        else 
           []      




(***************************************************************************************************************)

fun strc([], bracket , ss , temp , i , prev)=
        if(ss=0 andalso List.length(temp) <> 0)
          then drop(temp,1)
        else if(ss=1)
           then if( bracket = 1 )
               then temp@[~7]
               else 
                  temp 
        else 
           []           
    | strc(l:int list, bracket , ss , temp , i , prev) =
       if(ss = 1)
         then if(isDigit(hd(l)) orelse hd(l)= ~6   orelse  hd(l)= ~1)           
                 then strc(tl(l),bracket , ss , temp@[hd(l)] , i+1 , hd(l) )
             else if( hd(l) = ~8 andalso prev = ~6 andalso bracket = 1 )
                  then take(List.length(temp)-1,temp)@[~7]@[~6]@[hd(l)]@strc(tl(l),0 ,0 , [] , i+1, hd(l))

             else if( hd(l) = ~8 andalso prev = ~1 andalso bracket = 1 )
                  then take(List.length(temp)-1,temp)@[~7]@[~1]@[hd(l)]@strc(tl(l),0,ss, [],i+1,hd(l))
             else 
                 if(bracket= 1)
                    then temp@[~7]@[hd(l)]@strc(tl(l),0,0,[],i+1,hd(l))
                 else 
                        temp@[hd(l)]@strc(tl(l),0,0,[],i+1,hd(l))
       else 
             if(hd(l) = ~6 orelse hd(l )= ~1)
                 then strc(tl(l),bracket,1,temp@[hd(l)],i+1,hd(l))
             else if(isDigit(hd(l))) 
                 then  if(i <> 0 andalso isDigit(prev))
                        then strc(tl(l),bracket,ss,temp@[hd(l)],i+1,hd(l))
                  else
                       strc(tl(l),1 ,ss ,temp@[~8]@[hd(l)],i+1,hd(l))
             else
                 if(List.length(temp) <> 0)
                   then  drop(temp,1) @ [hd(l)] @ strc(tl(l),0,ss, [],i+1,hd(l))
                 else
                     [hd(l)]@strc(tl(l),0,ss, [],i+1,hd(l))       

fun Interpreter() = 
   let 
      val input:string = valOf(TextIO.inputLine TextIO.stdIn)
      
    in
       print((toString(calc(zerogiver(strc(f(input),0,0,[],0,0),0,0))))^("\n"));
         Interpreter()
    end                                     
