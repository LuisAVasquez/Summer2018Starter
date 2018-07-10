(* ::Package:: *)

BeginPackage["InfiniteListsPackage`"]

(*There are three types of infinite lists:
direction 1 lists  : open on the right side, closed on the left side. 	Example: {1,2,3,4,5,....}
direction -1 lists: open on the left side, closed on the right side. 	Example: {....,-5,-4,-3,-2,-1}
direction 0 lists  : open on both sides:						Example: {...,-3,-2,-1,0,1,2,---}*)
InfiniteList[direction_,rule_][n_Integer]:= rule@n /;((direction==0)||(direction*n>0))
InfiniteList[direction_,rule_][n_Integer]:=
Failure["InvalidInfinitePart",<|"MessageTemplate"->"Invalid infinite part specification"|>]/;Not@((direction==0)||(direction*n>0))


(*Attention: Most of the functions are analogous to the ones already in the Wolfram Language, 
and they have "Infinite" added before the existing name*)

(*Prepend only works for direction 1*)
InfinitePrepend[InfiniteList[direction_,rule_],elem_]:=
With[{newrule= If[#==1,elem,rule@(#-1)]&
}, InfiniteList[direction,newrule]]/;(direction==1 );

InfinitePrepend[InfiniteList[direction_,rule_],elem_]:=
Failure["InvalidInfinitePrepend",<|"MessageTemplate"->"InfinitePrepend only defined for right-open infinite lists"|>]/;(direction!= 1 );



(*Append only works for direction -1*)
InfiniteAppend[InfiniteList[direction_,rule_],elem_]:=
With[{newrule= If[#==-1,elem,rule@(#+1)]&
}, InfiniteList[direction,newrule]]/;(direction==-1 );

InfiniteAppend[InfiniteList[direction_,rule_],elem_]:=
Failure["InvalidInfinitePrepend",<|"MessageTemplate"->"InfinitePrepend only defined for left-open infinite lists"|>]/;(direction!= -1 );



InfinitePart[InfiniteList[direction_,rule_],n_Integer]:=rule@n /;((direction==0)||(direction*n>0));

InfinitePart[InfiniteList[direction_,rule_],n_Integer]:=
Failure["InvalidInfinitePart",<|"MessageTemplate"->"Invalid infinite part specification"|>]/;Not@((direction==0)||(direction*n>0))



(*only integers can be taken as indexs!*)
InfinitePart[InfiniteList[direction_,rule_],list_List/;AllTrue[list,IntegerQ]]:=
InfinitePart[InfiniteList[direction,rule],list]=Map[rule,list]
InfinitePart[InfiniteList[direction_,rule_],list_List]:=Failure/;!AllTrue[list,IntegerQ]
(*this definitions needs to be refined! *)



(*Infinite Take, based on InfinitePart*)
InfiniteTake[InfiniteList[direction_,rule_],n_Integer]:=InfinitePart[InfiniteList[direction,rule],Range[n]]/;(direction==1&&n>0);
InfiniteTake[InfiniteList[direction_,rule_],n_Integer]:=InfinitePart[InfiniteList[direction,rule],Range[-1,n,-1]]/;(direction==-1 &&n<0);
(* for direction -1 lists, InfiniteTake[#,n] returns in the order {-1,-2,-3,...,-Abs[n]}  *)

InfiniteTake[InfiniteList[direction_,rule_],n_Integer]:=Failure/;Not@Or[(direction==1&&n>0),(direction==-1 &&n<0)]
InfiniteTake[InfiniteList[direction_,rule_],{n_Integer,m_Integer}]:= InfinitePart[InfiniteList[direction,rule],Range[n,m,1]]/;
(direction==1&& n<=  m);

InfiniteTake[InfiniteList[direction_,rule_],{n_Integer,m_Integer}]:= InfinitePart[InfiniteList[direction,rule],Range[n,m,-1]]/;
(direction==-1&&m<=n<0);
 (*careful with the direction of the part in direction -1 lists!!*) 
(*InfiniteTake[mIL, {-4,-8}] = {mIL\[LeftDoubleBracket]-4\[RightDoubleBracket],mIL\[LeftDoubleBracket]-5\[RightDoubleBracket],...,mIL\[LeftDoubleBracket]-8\[RightDoubleBracket]}  *) (*mIL is an arbitrary direction -1 infinite list*)
(*with this implementation we have:     InfiniteTake[mIL,{-1,-Abs[n]}]= InfiniteTake[mIL,-Abs[n]]  *)
InfiniteTake[InfiniteList[direction_,rule_],{n_Integer,m_Integer}]:= InfinitePart[InfiniteList[direction,rule],Range[n,m,1]]/;
(direction==0&&  n<=m );
InfiniteTake[InfiniteList[direction_,rule_],{n_Integer,m_Integer}]:=
Failure/; Not@Or[(direction==1&& n<=  m),(direction==-1&&m<=n<0),(direction==0&&  n<=m )];

(*beginning work of the 04.07 for this definition*)
InfiniteTake[InfiniteList[direction_,rule_],{n_Integer,Infinity}]:=
With[{newrule=rule@(#+n-1)&},InfiniteList[direction,newrule]]/;(direction==1&&n>0);
InfiniteTake[InfiniteList[direction_,rule_],{n_Integer,Infinity}]:=Failure/;Not@(direction==1&&n>0||direction==0);	
InfiniteTake[InfiniteList[direction_,rule_],{-Infinity,n_Integer}]:=
With[{newrule=rule@(#+n+1)&},InfiniteList[direction,newrule]]/;(direction==-1&&n<0);
InfiniteTake[InfiniteList[direction_,rule_],{-Infinity,n_Integer}]:=Failure/;Not@(direction==-1&&n<0||direction==0);

InfiniteTake[InfiniteList[direction_,rule_],{-Infinity,Infinity}]:=InfiniteList[direction,rule]/;direction==0;
InfiniteTake[InfiniteList[direction_,rule_],{-Infinity,Infinity}]:=Failure/;Not@direction==0;		
(*notice that direction 0 lists can get direction 1 or -1 lists taken from them!*)
InfiniteTake[InfiniteList[0,rule_],{n_Integer,Infinity}]:=
	With[{newrule=rule@(#+n-1)&},InfiniteList[1,newrule]];
InfiniteTake[InfiniteList[0,rule_],{-Infinity,n_Integer}]:=
	With[{newrule=rule@(#+n+1)&},InfiniteList[-1,newrule]];
(*end of work of the 04.07 for this definition*)


InfiniteLength[InfiniteList[direction_,rule_]]=Infinity; (*by far the easiest*)



(*InfiniteDrop*)
InfiniteDrop[InfiniteList[direction_,rule_],n_Integer]:=
	With[{newrule= rule@(#+n)&},
	InfiniteList[direction,newrule]
]/;(direction==1 &&n>0);
InfiniteDrop[InfiniteList[direction_,rule_],n_Integer]:=
	With[{newrule= rule@(#+n)&}, (*"+n" even though n<0 *)
	InfiniteList[direction,newrule]
]/;(direction==-1 &&n<0);
InfiniteDrop[InfiniteList[direction_,rule_],n_Integer]:=Failure/; Not@Or[(direction==1 &&n>0),(direction==-1 &&n<0)]
InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer}]:=
	With[{newrule=(If[#<n,rule@#, rule@(#+1)])&},
	InfiniteList[direction,newrule]]/;(direction==1&&n>0);
InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer}]:=
	With[{newrule=(If[#>n,rule@#, rule@(#-1)])&},
	InfiniteList[direction,newrule]]/;(direction==-1&&n<0);
(*beginning work of the 05.07 on this definition*)
InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer,m_Integer}]:=
	With[{newrule=If[#<n,rule@#,rule@(#+m-n+1)]&},
		InfiniteList[direction,newrule]]/;(direction==1&&0<n<=m);
InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer,m_Integer}]:=
	With[{newrule=If[#>n,rule@#,rule@(#+m-n-1)]&},
InfiniteList[direction,newrule]]/;(direction==-1&&m<=n<0);

InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer,m_Integer}]:=
(*problems if range includes index 0*)
Module[{newrule},
	newrule=Which[ n>0,If[#<n,rule@#,rule@(#+m-n+1)]&,
				   m<0,If[#>m,rule@#,rule@(#+n-m-1)]&,
				True,If[#>=0,rule@(#+m+1),rule@(#+n)]&] ;
(*remember n<0 in this case*)
InfiniteList[direction,newrule] ]/;(direction==0&&n<=m);

InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer,m_Integer}]:=
Failure/;Not@Or[(direction==1&&0<n<=m),(direction==-1&&m<=n<0),(direction==0&&n<=m)];

InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer,Infinity}]:=
If[direction==1&&n==1,{},InfiniteTake[InfiniteList[direction,rule],n-1]]/;(direction==1&&n>0)
InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer,Infinity}]:=
With[{newrule=rule@(#+n)&}, InfiniteList[-1,newrule]]/;direction==0
InfiniteDrop[InfiniteList[direction_,rule_],{n_Integer,Infinity}]:=Failure/;Not@Or[direction==0,(direction==1&&n>0)]
InfiniteDrop[InfiniteList[direction_,rule_],{-Infinity,n_Integer}]:=
If[direction==-1&&n==-1,{},Reverse@InfiniteTake[InfiniteList[direction,rule],n+1]]/;(direction==-1&&n<0) (*remember the Reverse!*)
InfiniteDrop[InfiniteList[direction_,rule_],{-Infinity,n_Integer}]:=
With[{newrule=rule@(#+n)&},InfiniteList[1,rule]]/;direction==0
InfiniteDrop[InfiniteList[direction_,rule_],{-Infinity,n_Integer}]:=Failure/;Not@Or[direction==0,(direction==-1&&n<0)]
InfiniteDrop[InfiniteList[direction_,rule_],{-Infinity,Infinity}]:={}/;direction==0
InfiniteDrop[InfiniteList[direction_,rule_],{-Infinity,Infinity}]:=Failure/;direction!=0
(*end of work of 05.07 on this definition*)



(*First only makes sense for direction 1 lists*)
InfiniteFirst[InfiniteList[direction_,rule_]]:=rule@1/;direction==1
InfiniteFirst[InfiniteList[direction_,rule_]]:=Failure/;direction!=1

(*last only makes sense for direction -1 lists*)
InfiniteLast[InfiniteList[direction_,rule_]]:=rule@(-1)/;direction==-1
InfiniteLast[InfiniteList[direction_,rule_]]:=Failure/;direction!= -1
(*InfiniteDirection returns the direction of the list*)
InfiniteDirection[InfiniteList[direction_,rule_]]:=direction;

(*InfiniteRange, Infinite Reverse*)
InfiniteRange[n_Integer,Infinity]:=InfiniteList[1,x\[Function]x+n-1];
InfiniteRange[-Infinity,n_Integer]:=InfiniteList[-1,x\[Function]x+n+1];
InfiniteRange[-Infinity,Infinity]:=InfiniteList[0,x\[Function]x];

InfiniteReverse[InfiniteList[direction_,rule_]]:=
With[{newrule=rule@(-#)&},InfiniteList[-direction,newrule]]


(*Infinite Join*)
InfiniteJoin[list_List,InfiniteList[direction_,rule_]]:=
With[{newrule=If[#<= Length[list],list[[#]],rule@(#-Length[list])]&},
InfiniteList[direction,newrule]]/;direction==1
InfiniteJoin[list_List,InfiniteList[direction_,rule_]]:=Failure/;Not@direction==1

InfiniteJoin[InfiniteList[direction1_,rule1_],InfiniteList[direction2_,rule2_]]:=
With[{newrule=If[#<0,rule1@#,rule2@(#+1)]&},
InfiniteList[0,newrule]]/;(direction1==-1&&direction2==1)
InfiniteJoin[InfiniteList[direction1_,rule1_],InfiniteList[direction2_,rule2_]]:= Failure/;Not@(direction1==-1&&direction2==1)
InfiniteJoin[InfiniteList[direction_,rule_],list_List]:=
With[{newrule= If[#>=-Length[list],list[[#]],rule@(#+Length[list]) ]&},
InfiniteList[direction,newrule]]/;direction==-1   
(*attention to the order:   Join[{...-3,-2,-1} ,{a,b,c,d}] ={...,-3,-2,-1,a,b,c,d} . NOT {...,-3,-2,-1,d,c,b,a} *) 
(*think of it as pasting one after the other*)
InfiniteJoin[InfiniteList[direction_,rule_],list_List]:=Failure/;direction!=-1



(*InfiniteRealDigits*)
(*this one seems very inefficient*)
(*returns a list of two elements: First the infinite list of the digits, Second the number of digits to the left of the decimal point*)
InfiniteRealDigits[x_/;x\[Element]Reals,b_:10]:=
With[{rule= Last@First@RealDigits[x,b,#]&},
{InfiniteList[1,rule],RealDigits[x,b,Length[IntegerDigits@Floor[x]]][[2]]}]
InfiniteRealDigits[E][[1]] //InfiniteTake[#,10]&//AbsoluteTiming (*before modification*)
{0.0008095322421513319`,{2,7,1,8,2,8,1,8,2,8}}
InfiniteRealDigits[E][[1]] //InfiniteTake[#,10]&//AbsoluteTiming (*after modification*)
{0.00012648941283614561`,{2,7,1,8,2,8,1,8,2,8}}
InfiniteRealDigits[E,2][[2]]
2



(*InfiniteRest, InfiniteMost *)
(*Rest only makes sense for direction 1 lists*)
InfiniteRest[InfiniteList[direction_,rule_]]:=With[{newrule=rule@(#+1)&},InfiniteList[direction,newrule]]/;direction==1;
InfiniteRest[InfiniteList[direction_,rule_]]:=Failure/;direction!= 1;
(*Most only makes sense for direction -1 lists*)
InfiniteMost[InfiniteList[direction_,rule_]]:=With[{newrule=rule@(#-1)&},InfiniteList[direction,newrule]]/;direction==-1
InfiniteMost[InfiniteList[direction_,rule_]]:=Failure/;direction!= -1



(*InfiniteRiffle*)
InfiniteRiffle[InfiniteList[direction_,rule_],x_]:=
With[{newrule=If[Mod[direction*#,2]==1,rule@((#+direction)/2),x]&
 (*#+direction: I use this not to write #+1 for direction 1 lists or #-1 for -1 lists*)
},InfiniteList[direction,newrule]]/;(direction==1||direction==-1)
InfiniteRiffle[InfiniteList[direction_,rule_],x_]:=
With[{newrule=If[Mod[#,2]==1,x,rule@(#/2)]&},InfiniteList[direction,newrule]]/;direction==0





(*InfiniteSelectRule, InfiniteSelect*)
(*First I'm implementing a way to get the nth element that satisfies an specific condition*)
InfiniteSelectRule[1,rule_,condition_][n_Integer]:= InfiniteSelectRule[1,rule,condition][n]= (*direction 1 assumes n>0*)
	Module[{countCases=0,i=1},
	While[countCases<n, If[condition[rule@i]==True,countCases++];i++];
	rule@(i-1)
]
InfiniteSelectRule[-1,rule_,condition_][n_Integer]:= InfiniteSelectRule[-1,rule,condition][n]= (*direction -1 assumes n<0*)
	Module[{countCases=0,i=1},
	While[countCases<-n,If[condition[rule@(-i)]==True,countCases++];i++];
	rule@(-i+1)
]
InfiniteSelect[InfiniteList[direction_,rule_],condition_]:=
InfiniteList[direction,InfiniteSelectRule[direction,rule,condition][#]&]/;direction==1
InfiniteSelect[InfiniteList[direction_,rule_],condition_]:=
InfiniteList[direction,InfiniteSelectRule[direction,rule,condition][#]&]/;direction==-1
(*Beginning of work of the 06.07 for this definition*)
InfiniteSelect[InfiniteList[direction_,rule_],condition_]:=
With[{newrule= If[#>=0,InfiniteSelectRule[1,rule,condition][#],InfiniteSelectRule[-1,rule,condition][#]]&},
InfiniteList[direction,newrule]]/;direction==0;


(*first a really inefficient implementation: Use MatchQ*)
InfiniteCases[InfiniteList[direction_,rule_],pattern_]:=
InfiniteSelect[InfiniteList[direction,rule],MatchQ[#,pattern]&]


(*this returns the rule of the list*)
InfiniteRule[InfiniteList[direction_,rule_]]:=rule


(*InfiniteFirstPosition*)
(*this function gives the first position (in absolute value for direction 0) of the element that matches the pattern*)
(*It is not guaranteed to finish*)
InfiniteFirstPosition[InfiniteList[direction_/;(direction==1||direction==-1),rule_],pattern_]:=
InfiniteFirstPosition[InfiniteList[direction,rule],pattern]=
Module[{i=1},
While[Not@MatchQ[rule@(direction*i),pattern],i++];
i*direction
]
InfiniteFirstPosition[InfiniteList[direction_/;direction==0,rule_],pattern_]:=
InfiniteFirstPosition[InfiniteList[direction,rule],pattern]=
Module[{i=0,index=0},
While[Not@MatchQ[rule@index,pattern],
i++;index=((-1)^i)*Floor[i/2];
];(*this makes index= 0,1,-1,2,-2,3,-3,....*)
index
]



(*InfiniteUnequal*)
(*This returns True if the infinite lists are Unequal. Sadly, with my algorithm, this is not guaranteed to end*)
InfiniteUnequal[InfiniteList[direction1_,rule1_],InfiniteList[direction2_,rule2_]]:=
Module[{i=1},
If[direction1!= direction2,Return[True]];
While[rule1@(direction1*i)==rule2@(direction2*i),i++];
Return[True]
]/;(direction1*direction2==1)
InfiniteUnequal[InfiniteList[direction1_,rule1_],InfiniteList[direction2_,rule2_]]:=
Module[{i=0,index=0},
If[direction1!=direction2,Return[True]];
While[rule1@index==rule2@index,
i++;index=((-1)^i)*Floor[i/2];];
]/;(direction1*direction2==0)



(*InfinitePlus,InfiniteTimes, InfiniteSum*)
(*when involving two infinite lists, this operations are componentwise*)
InfinitePlus[alpha_Real,InfiniteList[direction_,rule_]]:=InfiniteList[direction,(alpha+rule@#)&]
InfinitePlus[alpha_Integer,InfiniteList[direction_,rule_]]:=InfiniteList[direction,(alpha+rule@#)&]
InfiniteTimes[alpha_Real,InfiniteList[direction_,rule_]]:=InfiniteList[direction,(alpha*rule@#)&]
InfiniteTimes[alpha_Integer,InfiniteList[direction_,rule_]]:=InfiniteList[direction,(alpha*rule@#)&]
InfinitePlus[InfiniteList[direction1_,rule1_],InfiniteList[direction2_,rule2_]]:=
InfiniteList[direction1,(rule1@#+rule2@#)&]/;direction1==direction2
InfiniteTimes[InfiniteList[direction1_,rule1_],InfiniteList[direction2_,rule2_]]:=
InfiniteList[direction1,((rule1@#)*(rule2@#))&]/;direction1==direction2

(*InfiniteSum gives the infinite list of partial sums (only for direction 1 and -1)*)
InfiniteSum[InfiniteList[direction_/;(direction==1||direction==-1),rule_]]:=
InfiniteSum[InfiniteList[direction,rule]]=
With[{newrule=
Sum[rule[i],{i,direction,#1,direction}]&
(*If[#\[Equal]1,rule[1],rule[#]+newrule[#-1]]&*) (*recursive implementation doesn't work*)
},InfiniteList[direction,newrule]]



(*InfiniteEqual*)
(*not guaranteed to finish*)
InfiniteEqual[InfiniteList[direction1_,rule1_],InfiniteList[direction2_,rule2_]]:=
Module[ {(*auxstring*)},
If[direction1!=direction2,Return[False]];
(*auxstring=(tostring[rule1]<>"=="<>tostring[rule2]);*)
Which[
TrueQ@Resolve[ForAll[x,rule1[x]==rule2[x]]],
Return[True],
TrueQ@FullSimplify[ForAll[x,rule1[x]==rule2[x]]],
Return[True],
Quiet@FindInstance[ForAll[x,rule1[x]!=rule2[x] ],{x}]!=  {},
Return[False],
True,
Return[Failure]
]      
]



(*InfiniteAnd, InfiniteOr*)
(*conjunction/disjunction of the elements of the list*)
InfiniteAnd[InfiniteList[direction_,rule_],domain_]:=TrueQ@FullSimplify[rule[x],Element[x,domain]] 


InfiniteAnd2[InfiniteList[direction_,rule_],condition_]:=TrueQ@FullSimplify[rule[x],condition[x]] 
InfiniteOr[InfiniteList[direction_,rule_],condition_,domain_]:=
TrueQ@Quiet@Resolve[Exists[x,FullSimplify[rule[x],condition[x]]],domain]
InfiniteOr[InfiniteList[direction_,rule_],condition_]:=
TrueQ@Quiet@Resolve[Exists[x,FullSimplify[rule[x],condition[x]]]]




(* InfiniteMatrix, InfiniteTake (for infinite matrices)*)
(*Infinite matrices are infinite lists of their rows, which are also infinite lists*)
InfiniteMatrix[rule_]:=
InfiniteList[1, Function[x,InfiniteList[1, Function[y,rule[x,y]]]]]

InfiniteTake[InfiniteMatrix[rule_],{n1_Integer?Positive,n2_Integer?Positive},{m1_Integer?Positive,m2_Integer?Positive}]:=
Table[    InfiniteTake[  InfinitePart[ InfiniteMatrix[rule]  ,n]       ,{m1,m2}]           ,{n,n1,n2,1}]

InfiniteTake[InfiniteMatrix[rule_],n_Integer?Positive,m_Integer?Positive]:=InfiniteTake[InfiniteMatrix[rule],{1,n},{1,m}]



(*InfiniteMatrixPlus, InfiniteMatrixTimes*)
InfiniteMatrixPlus[InfiniteMatrix[rule1_],InfiniteMatrix[rule2_]]:= InfiniteMatrix[rule1[#1,#2]+rule2[#1,#2]&]
InfiniteMatrixTimes[alpha_Integer,InfiniteMatrix[rule_]]:= InfiniteMatrix[Times[alpha,rule[#1,#2]]&]
InfiniteMatrixTimes[alpha_Real,InfiniteMatrix[rule_]]:=        InfiniteMatrix[Times[alpha,rule[#1,#2]]&]
(*Because of the infinite sum, Matrix multiplication  is (most of the times) only simbolically defined*)

InfiniteMatrixTimes[InfiniteMatrix[rule1_],InfiniteMatrix[rule2_]]:=With[
{newrule= Sum[Times[rule1[#1,k],rule2[k,#2]],{k,1,Infinity}]&},
InfiniteMatrix[newrule]]




(*InfinitePolyTimes*)
(*multiplication of infinite polynomials!*)
InfinitePolyTimes[InfiniteList[1,rule1_],InfiniteList[1,rule2_]]:=
With[{newrule=Sum[Times[rule1[j],rule2[#+1-j]],{j,1,#}]&
},InfiniteList[1,newrule]]
(*the term #+1-j is there because I have defined infinite lists of direction 1 as starting with index 1*)





(*InfiniteCellularAutomaton*)
(*this is a cellular automaton that accepts an infinite list as an initial condition, 
it is a direction 1 infinite list, of direction 0 infinite lists.*)

ClearAll[InfiniteCellularAutomatonStep];Clear[InfiniteCellularAutomatonStep];Clear[InfiniteCellularAutomaton];
ClearAll[InfiniteCellularAutomaton]
InfiniteCellularAutomatonStep[cellularrule_,InfiniteList[0,rule_ ]]:=
With[{newrule=Part[CellularAutomaton[cellularrule,{rule@(#-1),rule@#,rule@(#+1)}],2]&
}, InfiniteList[0,newrule]]

InfiniteCellularAutomatonStep[cellularrule_,InfiniteList[0,rule_],n_Integer]:=
NestList[InfiniteCellularAutomatonStep[cellularrule,#]&,InfiniteList[0,rule],n]

InfiniteCellularAutomatonStep[cellularrule_,InfiniteList[0,rule_],1]:=InfiniteList[0,rule]

InfiniteCellularAutomaton[cellularrule_,InfiniteList[0,rule_]]:=
InfiniteList[1,InfiniteCellularAutomatonStep[cellularrule,InfiniteList[0,rule],#]&]

InfiniteCellularAutomatonData1[cellularrule_,InfiniteList[0,rule_],{n1_,n2_},t_]:=
Map[InfiniteTake[#,{n1,n2}]&,InfiniteCellularAutomaton[cellularrule,InfiniteList[0,rule]][t]]

InfiniteCellularAutomatonData1[cellularrule_,InfiniteList[0,rule_],n_,t_]:=
InfiniteCellularAutomatonData1[cellularrule,InfiniteList[0,rule],{-n,n},t]

InfiniteCellularAutomatonPlot1[cellularrule_,InfiniteList[0,rule_],{n1_,n2_},t_]:=
ArrayPlot[InfiniteCellularAutomatonData1[cellularrule,InfiniteList[0,rule],{n1,n2},t]]

InfiniteCellularAutomatonPlot1[cellularrule_,InfiniteList[0,rule_],n_,t_]:=
ArrayPlot[InfiniteCellularAutomatonData1[cellularrule,InfiniteList[0,rule],n,t]]

InfiniteCellularAutomatonData2[cellularrule_,InfiniteList[0,rule_],{n1_,n2_},t_]:=
CellularAutomaton[cellularrule,InfiniteTake[InfiniteList[0,rule],{n1,n2}],t]

InfiniteCellularAutomatonData2[cellularrule_,InfiniteList[0,rule_],n_,t_]:=
InfiniteCellularAutomatonData2[cellularrule,InfiniteList[0,rule],{-n,n},t]

InfiniteCellularAutomatonPlot2[cellularrule_,InfiniteList[0,rule_],{n1_,n2_},t_]:=
ArrayPlot[InfiniteCellularAutomatonData2[cellularrule,InfiniteList[0,rule],{n1,n2},t]]

InfiniteCellularAutomatonPlot2[cellularrule_,InfiniteList[0,rule_],n_,t_]:=
ArrayPlot[InfiniteCellularAutomatonData2[cellularrule,InfiniteList[0,rule],n,t]]






EndPackage[]
