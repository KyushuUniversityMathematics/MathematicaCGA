(* ::Package:: *)

(* ::Title:: *)
(*OrigamiPackage.m*)


(* ::Text:: *)
(*Copyright (c) 2015  Mitsuhiro Kondo , Takuya Matsuo , Yoshihiro Mizoguchi , Hiroyuki Ochiai , Kyushu University*)
(**)
(**)
(*Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell*)
(*copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:*)
(*The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.*)
(*THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.*)


(* ::Text:: *)
(*\:6700\:7d42\:66f4\:65b0\:65e5:2016/02/14*)
(*\:4f5c\:6210\:65e5:2015/06/01 *)


(* ::Text:: *)
(*\:540c\:540d\:306e\:30b7\:30f3\:30dc\:30eb\:306e\:7af6\:5408\:3092\:907f\:3051\:308b\:305f\:3081\:30b3\:30f3\:30c6\:30ad\:30b9\:30c8\:3092\:5b9a\:3081\:308b*)


BeginPackage["OrigamiPackage`"];


(* ::Text:: *)
(*\:6298\:308a\:7d19\:5b9a\:7406*)


Ori1[P_,Q_,x_,y_]:=Module[{},(Q-P).{y-P[[2]],-x+P[[1]]}];
Ori2[P_,Q_,x_,y_]:=Module[{},(Q-P).{x-(P[[1]]+Q[[1]])/2,y-(P[[2]]+Q[[2]])/2}];



Ori1[P_,Q_]:=(Q-P).{#[[2]]-P[[2]],-#[[1]]+P[[1]]}&;
Ori2[P_,Q_]:=(Q-P).{#[[1]]-(P[[1]]+Q[[1]])/2,#[[2]]-(P[[2]]+Q[[2]])/2}&;
p2line[P3_,P4_]:=(P4-P3).{#[[2]]-P3[[2]],-#[[1]]+P3[[1]]}&;


p2line[P3_,P4_]:=p2line[P3,P4,#[[1]],#[[2]]]&;
p2line[P3_,P4_,x_,y_]:=Module[{},(P4-P3).{y-P3[[2]],-x+P3[[1]]}];

Kouten2[m_,n_]:=Module[{Ans,x,y},Ans=Solve[m[{x,y}]==0&&n[{x,y}]==0,{x,y}];
If[Ans!= {},{x,y}/.Ans[[1]] ,{}]
];


Ori3[m_,n_]:=Ori3[m,n,#[[1]],#[[2]]]&;
Ori3[m_,n_,flag_]:=Ori3[m,n,#[[1]],#[[2]]][[flag]]&;

Ori3[m_,n_,x_,y_]:=Module[{Ans,K,U,V,W1,W2},
K=Kouten2[m,n];
If[K!= {},
U={Coefficient[m[{x,y}],y],-Coefficient[m[{x,y}],x]};
U=U/Norm[U];
V={Coefficient[n[{x,y}],y],-Coefficient[n[{x,y}],x]};
V=V/Norm[V];
W1=(U+V)/2;
W2={W1[[2]],-W1[[1]]};
Ans={((W1).{y-K[[2]],-x+K[[1]]}),((W2).{y-K[[2]],-x+K[[1]]})}
 ,{}]
];



Ori4[P_,m_]:=Ori4[P,m,#[[1]],#[[2]]]&;
Ori4[P_,m_,x_,y_]:=Module[{U},
U={Coefficient[m[{x,y}],y],-Coefficient[m[{x,y}],x]};
(U).{x-P[[1]],y-P[[2]]}];


Ori5[P_,Q_,m_]:=Ori5[P,Q,m,#[[1]],#[[2]]]&;
Ori5[P_,Q_,m_,flag_]:=Ori5[P,Q,m,#[[1]],#[[2]]][[flag]]&;

Ori5[P_,Q_,m_,x_,y_]:=Module[{Ans,a,b,c,T1,T2,T3,i},

T1={x,y}/.Solve[(  a (x-P[[1]])+( y-P[[2]])==0 )&&
(parabola[Q,m,x,y]==0),{x,y}];
T2=Solve[(T1[[1]][[1]]==T1[[2]][[1]])&&(T1[[1]][[2]]==T1[[2]][[2]]),Reals ];
Print[T2];
T3=( ( a (x-P[[1]])+( y-P[[2]]))/.T2)

];


parabola[P1_,P3_,P4_]:=parabola[P1,P3,P4,#[[1]],#[[2]]]&;
parabola[P1_,P3_,P4_,x_,y_]:=Module[{},((P4-P3).{y-P3[[2]],-x+P3[[1]]})^2/Norm[(P4-P3)]^2-
(  (x-P1[[1]])^2+(y-P1[[2]])^2  )];

parabola[P_,m_]:=parabola[P,m,#[[1]],#[[2]]]&;
parabola[P_,m_,x_,y_]:=Module[{a,b,c},
a=Coefficient[m[{x,y}],x];
b=Coefficient[m[{x,y}],y];
c=m[{x,y}]-a x-b y;
(m[{ x ,y}])^2/(a^2+b^2)-
(  (x-P[[1]])^2+(y-P[[2]])^2  )];


Ori6[P_,m_,Q_,n_]:=Ori6[P,m,Q,n,#[[1]],#[[2]]]&;
Ori6[P_,m_,Q_,n_,flag_]:=Ori6[P,m,Q,n,#[[1]],#[[2]]][[flag]]&;

Ori6[P_,m_,Q_,n_,x_,y_]:=Module[{Ans,a,b,c,T1,T2,S1,S2,U1,U2,i},

T1={x,y}/.Solve[(  a x+b y+c==0 )&&
(parabola[P,m,x,y]==0),{x,y}];
T2={a,b,c}/.Solve[(T1[[1]][[1]]==T1[[2]][[1]])&&(T1[[1]][[2]]==T1[[2]][[2]]) ];

S1={x,y}/.Solve[( a x+b y+c==0 )&&
(parabola[Q,n,x,y]==0),{x,y}];
S2={a,b,c}/.Solve[(S1[[1]][[1]]==S1[[2]][[1]])&&(S1[[1]][[2]]==S1[[2]][[2]]) ];

U1=NSolve[(T2[[1]][[1]]==S2[[1]][[1]])&&(T2[[1]][[2]]==S2[[1]][[2]])
     &&(T2[[1]][[3]]==S2[[1]][[3]]),Reals];
U2=S2[[1]]/.U1;
Ans=Table[{x,y,1}.U2[[i]],{i,1,Length[U2],1}]

];


Ori7[P_,m_,n_]:=Ori7[P,m,n,#[[1]],#[[2]]]&;
Ori7[P_,m_,n_,x_,y_]:=Module[{D,U,m2,MP},

U={Coefficient[m[{x,y}],y],-Coefficient[m[{x,y}],x]};
m2[{x0_,y0_}]:=(U).{y0-P[[2]],-x0+P[[1]]};
MP=(Kouten2[m2,n]+P)/2;
(U).{x-MP[[1]],y-MP[[2]]}
];


Ori1::usage="Ori1[P_,Q_,x_,y_] \:ff12\:70b9P,Q\:4e0a\:3092\:901a\:308b\:6298\:308a\:7ddar[x_,y_](==0)\:3092\:6c42\:3081\:308b.";
Ori2::usage="Ori2[P_,Q_,x_,y_] \:70b9P\:304c\:70b9Q\:306b\:91cd\:306a\:308b\:6298\:308a\:7ddar[x_,y_](==0)\:3092\:6c42\:3081\:308b.";
Ori3::usage="Ori3[m_,n_,x_,y_] \:7ddam\:304c\:7ddan\:4e0a\:306b\:91cd\:306a\:308b\:6298\:308a\:7ddar[x_,y_](==0)\:3092\:6c42\:3081\:308b(2\:672c).";
Ori4::usage="Ori4[P_,m_,x_,y_] \:7ddam\:306b\:5782\:76f4\:3067\:70b9P\:3092\:901a\:308b\:6298\:308a\:7ddar[x_,y_](==0)\:3092\:6c42\:3081\:308b.";
Ori5::usage="Ori5[P_,Q_,m_,x_,y_] \:70b9P\:304c\:7ddam\:4e0a\:306b\:91cd\:306a\:308a,\:70b9Q\:4e0a\:3092\:901a\:308b\:6298\:308a\:7ddar[x_,y_](==0)\:3092\:6c42\:3081\:308b(0~2\:672c).";
Ori6::usage="Ori6[P_,m_,Q_,n_,x_,y_] \:70b9P\:304c\:7ddam\:4e0a\:306b\:91cd\:306a\:308a,\:70b9Q\:304c\:7ddan\:4e0a\:306b\:91cd\:306a\:308b\:6298\:308a\:7ddar[x_,y_](==0)\:3092\:6c42\:3081\:308b(0~3\:672c).";
Ori7::usage="Ori7[P_,m_,n_,x_,y_] \:7ddam\:306b\:5782\:76f4\:3067,\:70b9P\:304c\:7ddan\:4e0a\:306b\:91cd\:306a\:308b\:6298\:308a\:7ddar[x_,y_](==0)\:3092\:6c42\:3081\:308b.";


p2line::usage="p2line[P3_,P4_,x_,y_] \:ff12\:70b9P3,P4\:4e0a\:3092\:901a\:308b\:76f4\:7ddam[x_,y_](==0)\:3092\:6c42\:3081\:308b.";
Kouten2::usage="Kouten2[m_,n_] \:7ddam\:3068\:7ddan\:306e\:4ea4\:70b9\:306e\:5ea7\:6a19\:3092\:6c42\:3081\:308b( \:5e73\:884c\:306a\:5834\:5408\:306f\:7a7a\:96c6\:5408 {} ).";
parabola::usage="parabola[P_,m_,x_,y_] \:7126\:70b9P,\:6e96\:7ddam\:306e\:653e\:7269\:7ddaf[x_,y_](==0)\:3092\:6c42\:3081\:308b.
parabola[P1_,P3_,P4_,x_,y_] \:7126\:70b9P,\:6e96\:7ddaP3P4\:306e\:653e\:7269\:7ddaf[x_,y_](==0)\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*FaceDivide*)


FaceDivide[F_,A_,Ic_,m_]:=Module[{A1,Ic0,F0,,F1,A0,Al04,i,L,R,Ai,j,Absi,RR,LL},
Ic0=Ic;
F0=F;F1=F0;A0=A;A1=A;
L=Association[{}];R=Association[{}];

While[Ic0!= {},
i=First[Ic0];
Al04=Algorithm04Re[F0,A0,i,m];
F0=Al04[[1]];A0=Al04[[2]];

If[Al04[[3]],
AssociateTo[L,i-> 2i];AssociateTo[R,i-> (2i+1)]
,(*0 or 1*)
(*\[DownArrow]F0&A0\:66f4\:65b0*)
If[Length[F0[2i]]<= 2,AssociateTo[R,i->i];
AppendTo[F0,i->F1[i]] ;KeyDropFrom[F0,{2i,(2i+1)}] ;
AppendTo[A0,i->A1[i]] ;KeyDropFrom[A0,{2i,(2i+1)}]  ];
If[KeyExistsQ[F0,2i+1] && Length[F0[(2i+1)]]<= 2,AssociateTo[L,i->i];
AppendTo[F0,i->F1[i]];KeyDropFrom[F0 ,{2i,(2i+1)}];
AppendTo[A0,i->A1[i]];KeyDropFrom[A0 ,{2i,(2i+1)}]   ]
];(*If_end*)

Ic0=Rest[Ic0];
];(*While_end*)

(*\:66f8\:304d\:63db\:3048\[DownArrow]*)
(*\:5de6\:306e\:3068\:304d*)
Ic0=Join[Values[L],
Complement[Union[Flatten[Map[A0[#]&,Values[L]]]](*\[LeftArrow]\:96a3\:63a5\:3057\:3066\:3044\:308b\:5de6\:306e\:8981\:7d20*),{0},Keys[L],Values[R]]];
Ic0=Intersection[Join[Keys[F0],Map[-#&,Keys[F0]]],Ic0];(*Ic0\:3092\:5b58\:5728\:3057\:3066\:3044\:308b\:9762\:3060\:3051\:306b\:9650\:5b9a*)

While[Ic0!= {},
i=First[Ic0];
Absi=Abs[i];
Ai=A0[Absi];
If[Sign[i]>0,LL=L,LL=Association[Flatten[Join[Map[#->-L[#]&,Keys[L]],Map[-#->-L[#]&,Keys[L]]]]]];
AssociateTo[A0,Absi->(Ai/.LL)];

Ic0=Rest[Ic0];
];(*While_end*)





(*\:53f3\:306e\:3068\:304d*)
Ic0=Join[Values[R],
Complement[Union[Flatten[Map[A0[#]&,Values[R]]]](*\[LeftArrow]\:96a3\:63a5\:3057\:3066\:3044\:308b\:53f3\:306e\:8981\:7d20*),{0},Keys[R],Values[L]]];
Ic0=Intersection[Join[Keys[F0],Map[-#&,Keys[F0]]],Ic0];(*Ic0\:3092\:5b58\:5728\:3057\:3066\:3044\:308b\:9762\:3060\:3051\:306b\:9650\:5b9a*)

While[Ic0!= {},
i=First[Ic0];
Absi=Abs[i];
Ai=A0[Absi];
If[Sign[i]>0,RR=R,RR=Association[Flatten[Join[Map[#->-R[#]&,Keys[R]],Map[-#->-R[#]&,Keys[R]]]]]];
AssociateTo[A0,Absi->(Ai/.RR)];

Ic0=Rest[Ic0];
];(*While_end*)


{F0,A0,Values[L],Values[R]}
];


FaceDivideOut[F_,A_,Ic_,m_,Range2_]:=Module[{Ans,i,LR0,F0},
Ans=FaceDivide[F,A,Ic,m];
F0=Ans[[1]];
Show[(* \[DownArrow]\:76f4\:7ddam *)
ContourPlot[m[{x,y}]==0,{x,Range2[[1]][[1]],Range2[[1]][[2]]},{y,Range2[[2]][[1]],Range2[[2]][[2]]}],

(* L *)
  If[(Length[Ans[[3]]]>=1),
LR0=Ans[[3]];
Table[{
Graphics[{
Dotted,Blue,Line[ Append[ F0[ LR0[[i]] ],First[ F0[ LR0[[i]] ] ]] ],
PointSize[Large],Blue,Point[ F0[ LR0[[i]] ] ],
Text[Style[Subscript["f", LR0[[i]]],Large,Bold,Blue],(Total[ F0[ LR0[[i]] ] ]/Length[ F0[ LR0[[i]] ] ])]
},PlotRange->Range2]
},{i,1,Length[ LR0 ],1} ]
,Graphics[]],

(* R *)
  If[(Length[Ans[[4]]]>=1),
LR0=Ans[[4]];
Table[{
Graphics[{
Dotted,Red,Line[ Append[ F0[ LR0[[i]] ],First[ F0[ LR0[[i]] ] ]] ],
PointSize[Large],Red,Point[ F0[ LR0[[i]] ] ],
Text[Style[Subscript["f", LR0[[i]]],Large,Bold,Red],(Total[ F0[ LR0[[i]] ] ]/Length[ F0[ LR0[[i]] ] ])]
},PlotRange->Range2]
},{i,1,Length[ LR0 ],1} ]
,Graphics[]],

(* \[DownArrow]\:76f4\:7ddam *)
ContourPlot[m[{x,y}]==0,{x,Range2[[1]][[1]],Range2[[1]][[2]]},{y,Range2[[2]][[1]],Range2[[2]][[2]]}]

 ](*Show_end*)
]



(*---Algorithm04Re----*)


SignQ[m_,Q_]:=If[Chop[m[Q]]>0,1, If[Chop[m[Q]]<0,-1,0] ];
p2line[P3_,P4_,x_,y_]:=Module[{},(P4-P3).{y-P3[[2]],-x+P3[[1]]}];
Kouten[P_,Q_,m_]:=Module[{x,y},{x,y}/.Solve[p2line[P,Q,x,y]==0&&m[{x,y}]==0,{x,y}][[1]]];

Alg4SortRe[f_,a_,seg_]:=Module[{F,g1,g2,A,b1,b2,X,Y,m,M},
If[Length[seg]>= 2,

X=seg[[1]];Y=seg[[2]];
m=Min[Position[f,X][[1]][[1]],Position[f,Y][[1]][[1]] ];
M=Max[Position[f,X][[1]][[1]],Position[f,Y][[1]][[1]] ];
If[m==1,
If[M==2,
A=a;F=f(* f={X,Y,...} *)
,(*M \[NotEqual] 1*)
b2=a[[ Length[a] ]];g2=f[[ Length[f] ]];
b1=Delete[a,-1];g1=Delete[f,-1];
A=Join[{b2},b1];F=Join[{g2},g1](* f={X,...,Y} *)
],(*m \[NotEqual] 1*)
b1=Table[a[[i]],{i,1,(m-1),1}];
g1=Table[f[[i]],{i,1,(m-1),1}];
b2=Table[a[[i]],{i,m,Length[a],1}];
g2=Table[f[[i]],{i,m,Length[f],1}];
A=Join[b2,b1];F=Join[g2,g1](* f={...,X,Y,...} *)
]
,(* Length[seg]\[Equal] 0 or 1 *)
If[Length[seg]==1,
X=seg[[1]];
m=Position[f,X][[1]][[1]];
(*\[DownArrow]\:59cb\:70b9\:3068\:7d42\:70b9\:304c\:540c\:3058Table\:306f\:7a7a\:96c6\:5408{}\:3068\:306a\:308b*)
b1=Table[a[[i]],{i,1,(m-1),1}];
g1=Table[f[[i]],{i,1,(m-1),1}];
b2=Table[a[[i]],{i,m,Length[a],1}];
g2=Table[f[[i]],{i,m,Length[f],1}];
A=Join[b2,b1];F=Join[g2,g1](* f={...,X,...} or {X} *)
,
A=a;F=f(* f={....} or {} *)
]

];(*If_end*)
{F,A}
];(*Alg4SortRe_end*)

Algorithm04Re[f_,A_,i_,m_]:=Module[{f0,f1,f2,a0,a1,a2,Ap,sgn,sgn2,seg,P,Q,X,x,y},
f0=f[i];a0=A[i];(*Input\:306f\:5b9a\:6570\:6271\:3044\:306a\:306e\:3067*)
sgn=SignQ[m,Last[f0]] ;(*1\:3064\:524d\:306e\:70b9\:306e\:5224\:5225*)
f1={};a1={};(*\:76f4\:7dda\:306e\:4e0b\:306e\:70b9\:96c6\:5408*)
f2={};a2={};(*\:76f4\:7dda\:306e\:4e0a\:306e\:70b9\:96c6\:5408*)
seg={};(*\:4ea4\:70b9\:306e\:96c6\:5408*)
While[f0!= {},
P=First[f0];Ap=First[a0];
sgn2=SignQ[m,P] ;(*\:73fe\:5728\:306e\:70b9\:306e\:5224\:5225*)

If[sgn2==1,
If[sgn==-1,
(*\:2460f1\[Rule]f2*)
If[f1!= {},Q=Last[f1],Q=Last[f0]];
(*1\:30b9\:30c6\:30c3\:30d7\:76ee\:3067\:4ea4\:5dee\:3059\:308b\:5834\:5408\:306b\:5099\:3048\:3066\[UpArrow]*)
X=Kouten[P,Q,m];
f1=Join[f1,{X}];a1=Join[a1,{Ap}];
f2=Join[f2,{X,P}];a2=Join[a2,{(*f1\[RightArrow]*)2i,Ap}];
seg=Append[seg,X]
,(*sgn \[NotEqual] -1*)
(*\:2461f2\[Rule]f2*)
f2=Append[f2,P] ;a2=Append[a2,Ap] 
],
(*sgn2 \[NotEqual] 1*)
If[sgn2==-1,
If[sgn==1,
(*\:2462f2\[Rule]f1*)
If[f2!= {},Q=Last[f2],Q=Last[f0]];
(*1\:30b9\:30c6\:30c3\:30d7\:76ee\:3067\:4ea4\:5dee\:3059\:308b\:5834\:5408\:306b\:5099\:3048\:3066\[UpArrow]*)
X=Kouten[P,Q,m];
f1=Join[f1,{X,P}];a1=Join[a1,{(*f2\[RightArrow]*)(2i+1),Ap}];
f2=Join[f2,{X}];a2=Join[a2,{Ap}];
seg=Append[seg,X]
,(*sgn \[NotEqual] 1*)
(*\:2463f1\[Rule]f1*)
f1=Append[f1,P] ;a1=Append[a1,Ap] 
],(*sgn2 = 0*)
(*\:2464f1 or f2\[Rule]\:76f4\:7dda *)
f1=Append[f1,P];f2=Append[f2,P];
If[sgn==-1,(*f1\[Rule]\:76f4\:7dda *)
a1=Append[a1,Ap] ;a2=Append[a2,(*f1\[RightArrow]*)2i]
,(*f2\[Rule]\:76f4\:7dda *)
a1=Append[a1,(*f2\[RightArrow]*)(2i+1)] ;a2=Append[a2,Ap]];
seg=Append[seg,P]
]
];(*If_end*)

f0=Rest[f0];a0=Rest[a0];
sgn=sgn2;
];(*While_end*)

{f1,a1}=Alg4SortRe[f1,a1,seg];
{f2,a2}=Alg4SortRe[f2,a2,seg];
(*\:7b2c3\:8981\:7d20\:306f\:5206\:5272\:3055\:308c\:305f\:304b\:3092\:8fd4\:3059*)
{ KeyDrop[ Append[f,{2i->f1,(2i+1)->f2}]  ,i],
 KeyDrop[ Append[A,{2i->a1,(2i+1)->a2}] ,i] ,
Length[f1]>=3 && Length[f2]>=3}

];


FaceDivide::usage="FaceDivide[F_,A_,Ic_,m_] \:9762\:306e\:9023\:60f3\:884c\:5217F,\:96a3\:63a5\:306e\:9023\:60f3\:884c\:5217A,\:5206\:5272\:5bfe\:8c61\:9762\:306eID\:30ea\:30b9\:30c8Ic,\:6298\:308a\:7ddam\:3092\:5165\:529b\:3068\:3057,
\:6298\:308a\:7dda\:3067\:5206\:5272\:3055\:308c\:305f\:6298\:308a\:7d19\:30b0\:30e9\:30d5G(={F2,A2,L,R})\:3092\:6c42\:3081\:308b.";
FaceDivideOut::usage="FaceDivideOut[F_,A_,Ic_,m_,Range2_] \:9762\:306e\:9023\:60f3\:884c\:5217F,\:96a3\:63a5\:306e\:9023\:60f3\:884c\:5217A,\:5206\:5272\:5bfe\:8c61\:9762\:306eID\:30ea\:30b9\:30c8Ic,\:6298\:308a\:7ddam\:3092\:5165\:529b\:3068\:3057,
\:6298\:308a\:7dda\:3067\:5206\:5272\:3055\:308c\:305f\:6298\:308a\:7d19\:3092\:7bc4\:56f2Range2( ={{X_min,X_max},{Y_min,Y_max}} )\:3067\:8868\:793a\:3059\:308b.";


SignQ::usage="SignQ[m_,Q_] \:70b9Q\:304c\:76f4\:7ddam[{x_,y_}](==0)\:306b\:5bfe\:3057\:3066\:4e0a\:306a\:30891,\:4e0b\:306a\:3089-1\:3092\:8fd4\:3059(\:76f4\:7dda\:4e0a\:306a\:30890).";
Kouten::usage="Kouten[P_,Q_,m_] \:7ddaPQ\:3068\:7ddam[{x_,y_}](==0)\:3068\:306e\:4ea4\:70b9\:306e\:5ea7\:6a19\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*FaceM*)


FaceM[G_,LR_,m_]:=Module[{LR0,F0,f1,f2,i,j,N,GM},
LR0=LR;F0=G["F"];
While[LR0!= {},
i=First[LR0];
f1=F0[i];
N=Length[f1];
f2=Table[Mirror[f1[[j]],m]  , {j,1,N,1}];
(*\[UpArrow]\:9006\:9806\:3067\:6642\:8a08\:56de\:308a\:3078*)

AppendTo[F0,i->f2] ;

LR0=Rest[LR0];
];(*While_end*)
GM=Append[G,<|"F"->F0|>]
];

FaceM[F0_,m_]:=Module[{LR0,f1,f2,i,j,N,GM},
LR0=LR;
While[LR0!= {},
i=First[LR0];
f1=F0[i];
N=Length[f1];
f2=Table[Mirror[f1[[j]],m]  , {j,1,N,1}];
(*\[UpArrow]\:9006\:9806\:3067\:6642\:8a08\:56de\:308a\:3078*)

AppendTo[F0,i->f2] ;

LR0=Rest[LR0];
];(*While_end*)
GM=Append[G,<|"F"->F0|>]
];

(*----------------------------------*)
Kouten2[m_,n_]:=Module[{Ans,x,y},Ans=NSolve[m[{x,y}]==0&&n[{x,y}]==0,{x,y}];
If[Ans!= {},{x,y}/.Ans[[1]] ,{}]
];

Mirror[P_,m_]:=Module[{M,U,n,x,y},
If[m[P]!= 0,
U={Coefficient[m[{x,y}],y],-Coefficient[m[{x,y}],x]};
n[{x_,y_}]:=(U).{x-P[[1]],y-P[[2]]};
M=Kouten2[m,n];
P+2(M-P)
,P]
];


(*\:9006\:9806\:3067\:53cd\:6642\:8a08\:56de\:308a\:3092\:4fdd\:6301*)
FaceMold[G_,LR_,m_]:=Module[{LR0,F0,f1,f2,A0,a1,a2,i,j,N,GM},
LR0=LR;F0=G["F"];A0=G["A"];
While[LR0!= {},
i=First[LR0];
f1=F0[i];a1=A0[i];
N=Length[f1];
f2=Table[Mirror[f1[[(N-j+1)]],m]  , {j,1,N,1}];
(*\[UpArrow]\:9006\:9806\:3067\:53cd\:6642\:8a08\:56de\:308a\:3092\:4fdd\:6301*)
N=Length[a1];
a2=Most[Prepend[Table[a1[[(N-j+1)]] , {j,1,N,1}],a1[[1]]]];
(*\:70b9\:306e\:9806\:756a\:306b\:5408\:308f\:305b\:3066\:96a3\:63a5\:95a2\:4fc2\:3092\:66f4\:65b0\:3000{1,2,3,4}\:306f{1,4,3,2}\:306b\:306a\:308b\:3053\:3068\:306b\:6ce8\:610f*)
AppendTo[F0,i->f2] ;AppendTo[A0,i->a2] ;

LR0=Rest[LR0];
];(*While_end*)
GM=Append[G,<|"F"->F0,"A"->A0|>]
];


FaceM::usage="FaceM[G_,LR_,m_] \:9762\:306eID\:96c6\:5408LR\:3092\:7ddam[{x_,y_}](==0)\:3067\:93e1\:6620\:3092\:3068\:308b.";


(* ::Text:: *)
(*OverLapJudge*)


CheckEdges[f_,g_,i_,j_]:=Module[{Ans,P1,P2,P3,Q1,Q2,Q3,Pk,Qk,n,m},
Ans=0;
n=Length[f];
m=Length[g];

P1=f[[Mod[i,n,1]]];
P2=f[[Mod[(i+1),n,1]]];
P3=f[[Mod[(i+2),n,1]]];
Q1=g[[Mod[j,m,1]]];
Q2=g[[Mod[(j+1),m,1]]];
Q3=g[[Mod[(j+2),m,1]]];

If[Chop[Det[{Q2-Q1,P2-P1}]]==0,(*\:5e73\:884c\:306e\:5834\:5408*)

If[Chop[Total[(Q2-Q1)(P2-P1)]]>0,(*\:540c\:3058\:5411\:304d*)
(*03*)
If[(Chop[Total[(Q2-P1)(P2-Q1)]]>0)&&(Chop[Det[{Q2-P1,P2-Q1}]]==0),
(*2\:3064\:306e\:8fba\:304c\:91cd\:306a\:308b \:304b\:3064 \:540c\:4e00\:76f4\:7dda*)Ans=3]
,(*\:9006\:5411\:304d*)
(*05*)
If[Chop[Det[{Q2-P1,P2-Q2}]]==0,
(*2\:3064\:306e\:8fba\:304c \:540c\:4e00\:76f4\:7dda*)Ans=5]
(*06*)
If[Chop[Det[{P2-P1,Q1-P1}]]<0,
(*Q1\:304c\:8fbaP1P2\:306e\:53f3\:5074*)Ans=6]
]

,(*\:5e73\:884c\:3067\:306a\:3044\:5834\:5408*)

Pk=Chop[Det[{Q2-Q1,Q1-P1}]/Det[{Q2-Q1,P2-P1}]];(*\:30d9\:30af\:30c8\:30ebP1P2\:306b\:5bfe\:3059\:308b\:4ea4\:70b9\:306e\:30d1\:30e9\:30e1\:30fc\:30bf*)
Qk=Chop[Det[{P2-Q1,P2-P1}]/Det[{Q2-Q1,P2-P1}]];(*\:30d9\:30af\:30c8\:30ebQ1Q2\:306b\:5bfe\:3059\:308b\:4ea4\:70b9\:306e\:30d1\:30e9\:30e1\:30fc\:30bf*)
(*01*)
If[(0<Pk<1)&&(0<Qk<1),Ans=1];
(*02*)
If[Xor[Pk==0,Qk==0],
If[((Qk==0)&&(0<Pk<1))&&(Chop[Det[{P2-P1,Q2-P1}]]>0),
(*Q2\:304c\:8fbaP1P2\:306e\:5de6\:5074*)Ans=2];
If[((Pk==0)&&(0<Qk<1))&&(Chop[Det[{Q2-Q1,P2-Q1}]]>0),
(*P2\:304c\:8fbaQ1Q2\:306e\:5de6\:5074*)Ans=2]
];
(*04*)
If[(Pk==1)&&(Qk==1),
If[(Chop[Det[{Q1-Q2,P1-Q2}]]>0)&&(Chop[Det[{Q2-Q1,P3-Q1}]]>0),
(*\:8fbaP1P2\:304c\:8fbaQ1Q2\:306e\:53f3\:5074 \:304b\:3064 \:8fbaP2P3\:304c\:8fbaQ1Q2\:306e\:5de6\:5074*)Ans=4];
If[(Chop[Det[{P1-P2,Q1-P2}]]>0)&&(Chop[Det[{P2-P1,Q3-P1}]]>0),
(*\:8fbaQ1Q2\:304c\:8fbaP1P2\:306e\:53f3\:5074 \:304b\:3064 \:8fbaQ2Q3\:304c\:8fbaP1P2\:306e\:5de6\:5074*)Ans=4]
];

];(*If_end*)

Ans
];



OverLapJudge[f_,g_]:=Module[{f0=f,g0=g,Ans,Ans2,t1,t2,i,j,n,m,k,P1,P2,Q1,Q2,a,b,c},
If[ClockWise[f]<0,f0=Reverse[f]];
If[ClockWise[g]<0,g0=Reverse[g]];
n=Length[f0];
m=Length[g0];
Ans=True;
t1=True;
t2=True;
i=1;
j=1;
While[(i<=n||j<=m)&&i<=2 n&&j<=2 m,k=CheckEdges[f0,g0,i,j];
If[1<=k<=4,Ans2=True;
Ans=False;
Break[]];
If[5<=k<=6,Ans2=False;
Ans=False;
Break[]];
If[k==0,P1=f0[[Mod[i,n,1]]];
P2=f0[[Mod[i+1,n,1]]];
Q1=g0[[Mod[j,m,1]]];
Q2=g0[[Mod[j+1,m,1]]];
t1=t1&&Chop[Det[{P2-P1,Q2-P2}]]>0;
t2=t2&&Chop[Det[{Q2-Q1,P2-Q2}]]>0;
a=Chop[Det[{P2-P1,Q2-Q1}]];
b=Chop[Det[{P2-P1,Q2-P2}]];
c=Chop[Det[{Q2-Q1,P2-Q2}]];
If[(a>=0&&b>=0)||(a<0&&c<0),i=i+1,j=j+1]]];
If[Ans,If[t1||t2,Ans2=True,Ans2=False]];Ans2];


OverLapJudge::usage="OverLapJudge[f_,g_] \:9762f,g\:306b\:91cd\:306a\:308a\:304c\:5b58\:5728\:3059\:308b\:306a\:3089True,\:3057\:306a\:3044\:306a\:3089False\:3092\:8fd4\:3059.";


(* ::Text:: *)
(*Peak*)


Peak[FKey_,S_]:=Complement[FKey,
Union[Map[#[[2]]&,Select[S,MemberQ[FKey,#[[1]]]&](*FKey\:3068\:95a2\:4fc2\:3042\:308bS\:3092\:62bd\:51fa*)]
(*\:4e0b\:306b\:3042\:308b\:9762*)](*\:91cd\:8907\:524a\:9664*)](*\:88dc\:96c6\:5408*);
(*FKey\:3068\:95a2\:4fc2\:3042\:308bS\:3092\:62bd\:51fa\[RightArrow]\[RightArrow]\:90e8\:5206\:96c6\:5408FKey\:306e\:4e2d\:3067\:306e\:91cd\:7573\:95a2\:4fc2\:3057\:304b\:8003\:616e\:3057\:306a\:3044*)
(*  Peak[ Keys[G["F"]] , G["S"]]  *)

Abyss[FKey_,S_]:=Complement[FKey,
Union[Map[#[[1]]&,Select[S,MemberQ[FKey,#[[2]]]&](*FKey\:3068\:95a2\:4fc2\:3042\:308bS\:3092\:62bd\:51fa*)]
(*\:4e0a\:306b\:3042\:308b\:9762*)](*\:91cd\:8907\:524a\:9664*)](*\:88dc\:96c6\:5408*);


Peak::usage="Peak[FKey_,S_] \:90e8\:5206\:96c6\:5408FKey\:306e\:9762\:306e\:9593\:3067\:306e\:91cd\:7573\:95a2\:4fc2S'(\[Subset]S)\:3067\:3001\:6700\:4e0a\:9762\:306e\:96c6\:5408.";
Abyss::usage="Abyss[FKey_,S_] \:90e8\:5206\:96c6\:5408FKey\:306e\:9762\:306e\:9593\:3067\:306e\:91cd\:7573\:95a2\:4fc2S'(\[Subset]S)\:3067\:3001\:6700\:4e0b\:9762\:306e\:96c6\:5408.";


SSimple[S_]:=Module[{S0,SG,i,j,High,iLow,iLow2,iLow3,D2,D1,t},
S0=S;
SG=GroupBy[S0,First->Last];
High=Keys[SG];

While[High!= {},

i=First[High];
iLow=SG[i];(*\[LeftArrow]\:7a7a\:96c6\:5408\:306f\:3042\:308a\:3048\:306a\:3044*)

iLow2=DeleteDuplicates[Flatten[ Lookup[SG,iLow,{}](*{}\:306e\:5e73\:5766\:5316*) ](*\:91cd\:8907\:524a\:9664*)];
iLow3={};
While[iLow2!= {},

j=First[iLow2];
If[KeyExistsQ[SG,j],iLow2=Union[iLow2,SG[j] ](*\:4e0b\:306e\:9762\:3092\:52a0\:3048\:308b*)];
iLow3=Union[iLow3,{j} ];
iLow2=Complement[iLow2,{j}](*j\:66f4\:65b0:\:5148\:982d\:304cj\:3067\:306a\:3044\:3068\:304d\:304c\:3042\:308b\:306e\:3067Rest\:306f\:99c4\:76ee*)
];(*While_iLow2*)

D2=Intersection[iLow,iLow3];(*\:524a\:9664\:5bfe\:8c61*)
D1=Table[{i,D2[[t]]},{t,1,Length[D2],1}];
S0=Complement[S0,D1];(*\:88dc\:96c6\:5408*)

High=Rest[High](*i\:66f4\:65b0*)
];(*While_High*)

S0
]


(* ::Text:: *)
(*new*)


MakeG[F_,A_,S_]:=<|"F"->F,"A"->A,"S"->S|>;


FCoordinate[G_,Key_]:=G["F"][Key];(*\:9762Key \:306e\:9802\:70b9\:5ea7\:6a19\:3092\:8fd4\:3059*)


(* ::Text:: *)
(**)


Trav[G_,K_,f_]:=
Module[{F=G["F"],S=G["S"],ekey,fkey,fP,AnsS,CoreTrav},
AnsS=S;
fkey=Keys[f][[1]];
fP=FCoordinate[G,fkey];(*\:52a0\:3048\:308b\:9762f \:306e\:5ea7\:6a19*)

CoreTrav[ekey_]:=Module[{eP,Succ={}},
eP=FCoordinate[G,ekey];(*\:9762e\:306e\:5ea7\:6a19*)
Succ=Union[Map[#[[2]]&,Select[S,ekey==#[[1]]&]]];(*\:9762e\:306e\:4e0b\:306e\:9762\:306e\:30ad\:30fc*)
If[OverLapJudge[fP,eP](*\:91cd\:7573\:95a2\:4fc2*),
(*True*)(*\:679d\:3092\:5897\:3084\:3059*)AnsS=Append[AnsS,{fkey,ekey}];Return[],
(*False*)(*\:4e0b\:3092\:898b\:308b*)Map[CoreTrav[#]&,Succ];Return[]
];
];

Map[CoreTrav[#]&,K];
Return[AnsS]
];

ApplyAddS[G_,K_,f_]:=
Module[{G0=G,S,fkey,K1},
S=Trav[G,K,f];(*Trav\:306b\:3088\:3063\:3066\:65b0\:3057\:3044S\:3092\:751f\:6210*)
fkey=Keys[f][[1]];
K1=Append[K,fkey];
K1=Complement[K1,Union[Map[#[[2]]&,Select[S,fkey==#[[1]]&]]]];
G0=Append[G0,<|"S"->S|>];
Return[{G0,K1}]
];



(* ::Text:: *)
(*ConsGraphByDivision*)


ConsGraphByDivision[G_,Ic_,m_]:=
Module[{GK,FALR,F=G["F"],A=G["A"],L,R,OldFKey,S=G["S"],G1,S1},
OldFKey=Keys[F];
FALR=FaceDivide[F,A,Ic,m];
F=FALR[[1]];
A=FALR[[2]];
L=FALR[[3]];
R=FALR[[4]];
G1=Append[G,<|"F"->F,"A"->A,"L"->L,"R"->R|>];
GK=GraphDivision[Append[G1,<|"S"->{}|>],{},OldFKey,S];
G1=GK[[1]];
S1=G1["S"];
S1=SSimple[S1];
Return[Append[G1,<|"S"->S1|>]]
];

GraphDivision[G_,K_,FKey_,S_]:=
Module[{GK,F=G["F"],S0=S,PeakF},
If[Length[FKey]==0,Return[{G,K}]];
PeakF=Peak[FKey,S][[1]];(*Fkey\:5185\:306e\:4e00\:756a\:4e0a\:306e\:9762\:306e\:30ad\:30fc*)
GK=GraphDivision[G,K,Complement[FKey,{PeakF}],S];
If[KeyExistsQ[F,PeakF],(*F\:306f\:5206\:5272\:5f8c\:306e\:9762\:306a\:306e\:3067, \:5b58\:5728\:3057\:306a\:3044\:3053\:3068\:306f\:5206\:5272\:3055\:308c\:305f\:3053\:3068\:3092\:610f\:5473\:3059\:308b.*)
GK=ApplyAddS[GK[[1]],GK[[2]],<|PeakF-> F[PeakF]|>],
GK=ApplyAddS[GK[[1]],GK[[2]],<|2PeakF-> F[2PeakF]|>];
GK=ApplyAddS[GK[[1]],GK[[2]],<|2PeakF+1-> F[2PeakF+1]|>]
];
Return[GK]
];


(* ::Text:: *)
(*ConsGraphByRotation*)


ConsGraphByRotation[G_,PiM_,\[Theta]_]:=
Module[{F,S,PiN,SM,SN,i,b,a,A,S1,G1,K1,GK},
F=G["F"];
S=G["S"];
PiN=Complement[Keys[F],PiM];
SM={};
SN={};

For[i=1,i<=Length[S],i++,
a=S[[i]][[1]];
b=S[[i]][[2]];
If[MemberQ[PiM,a]&&MemberQ[PiM,b],SM=Append[SM,{b,a}]];
If[MemberQ[PiN,a]&&MemberQ[PiN,b],SN=Append[SN,{a,b}]];
];
(*5\:301c9 \[CapitalPi]M \:3068\:3000\[CapitalPi]N \:306e\:4e2d\:3067\:91cd\:306a\:308a\:306e\:751f\:6210*)

If[\[Theta]>0,
A=PiM;
S1=SM;
G1=Append[G,<|"S"->SN|>];
K1=Peak[PiN,SN];
];
If[\[Theta]<0,
A=PiN;
S1=SN;
G1=Append[G,<|"S"->SM|>];
K1=Peak[PiM,SM];
];
(*10\:301c19 \:4e0a\:3068\:4e0b\:306b\:5206\:3051\:308b*)
GK=GraphRotation[G1,K1,A,S1];

G1=GK[[1]];
S1=G1["S"];
S1=SSimple[S1];
Return[Append[G1,<|"S"->S1|>]]
];

GraphRotation[G_,K_,FKey_,S_]:=
Module[{GK,F=G["F"],S0=S,A=FKey,PeakF},
If[Length[A]==0,Return[{G,K}]];
PeakF=Peak[A,S][[1]];
GK=GraphRotation[G,K,Complement[A,{PeakF}],S];
GK=ApplyAddS[GK[[1]],GK[[2]],<|PeakF-> F[PeakF]|>];
Return[GK]
];


(* ::Text:: *)
(*GOutput3D*)


GOutput3D[G_]:=Module[{Ans={  Graphics3D[{},Boxed->False]  },
i,Zcount=10,Kg,RestKey,FGraphics3D,G00,Key,ZCoordinate},

(*\:30b0\:30e9\:30d5G00\:306e\:9762Key\:3092\:9ad8\:3055ZCoordinate\:306b\:8868\:793a*)
FGraphics3D[G00_,Key_,ZCoordinate_]:=Module[{gCoordinate},
gCoordinate=Map[Append[#,ZCoordinate]&,FCoordinate[G00,Key]];

Graphics3D[{FaceForm[Yellow,Green],Polygon[gCoordinate]
,Text[Style[Subscript["f", (Key)],Large,Bold,Black],
 (Total[gCoordinate]/Length[gCoordinate])]}
,Boxed->False] 
];

RestKey=Keys[G["F"]];(*\:63cf\:304b\:308c\:3066\:3044\:306a\:3044\:9762\:306e\:30ad\:30fc*)
Kg=Peak[RestKey,G["S"]];(*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
While[Kg!= {},
(*\:30d4\:30fc\:30af\:306e\:9762\:3092\:8868\:793a*)
Ans=Join[Ans,Map[FGraphics3D[G,#,Zcount]&,Kg]];
RestKey=Complement[RestKey,Kg];
Kg=Peak[RestKey,G["S"]];
Zcount=Zcount-1;
];(*While_end*)

Show[Ans]
];



GOutput3D::usage="GOutput3D[G_] \:6298\:308a\:7d19\:30b0\:30e9\:30d5G\:306e\:8868\:793a.";


(* ::Text:: *)
(*GOutput3D02*)


(*\:30ec\:30a4\:30e4\:30fc\:3092\:540c\:5024\:985e\:3067\:307e\:3068\:3081\:308b*)
GOutput3D02[G_,width_,Moji_]:=GOutput3D02[G,width,Moji,True];
GOutput3D02[G_,width_,Moji_,order_]:=Module[{Ans={  Graphics3D[{},Boxed->False]  },
i,Zcount=10,LO,Kg,FGraphics3D,G00,Key,ZCoordinate,PiE},
Print["GOutput3D02"];

(*\:30b0\:30e9\:30d5G00\:306e\:9762Key\:3092\:9ad8\:3055ZCoordinate\:306b\:8868\:793a*)
FGraphics3D[G00_,Key_,ZCoordinate_]:=Module[{gCoordinate},
gCoordinate=Map[Append[#,ZCoordinate]&,FCoordinate[G00,Key]];
If[Moji,
Graphics3D[{FaceForm[Yellow,Green],Polygon[gCoordinate]
,Text[Style[Subscript["f", (Key)],Large,Bold,Black],(Total[gCoordinate]/Length[gCoordinate])]}
,Boxed->False] 
,(*False\:306e\:3068\:304d*)
Graphics3D[{FaceForm[Yellow,Green],Polygon[gCoordinate]}
,Boxed->False] 
]
];(*\[UpArrow]FGraphics3D\:5b9a\:7fa9*)



PiE=EquivalentDivision[Keys[G["F"]],G];(*\:540c\:5024\:985e\:306e\:30ad\:30fc*)
LO=LayerOrder[LayerGraph[PiE,G],order];(*\:9806*)

While[LO!= {},
i=First[LO];

Kg=Flatten[Table[
Select[PiE,(MemberQ[#,j]&)(*i\:3092\:542b\:3080PiE\:306e\:90e8\:5206\:3092\:62bd\:51fa*)][[1]](*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
,{j,i}]];(*\:540c\:3058\:540c\:5024\:985e\:306f\:307e\:3068\:3081\:3066\:8868\:793a*)
(*\:30d4\:30fc\:30af\:306e\:9762\:3092\:8868\:793a*)
Ans=Join[Ans,Map[FGraphics3D[G,#,Zcount]&,Kg]];

LO=Rest[LO];
Zcount=Zcount-width;
];(*While_end*)

Show[Ans]
];


GOutput3D02::usage="GOutput3D02[G_,width_,Moji_,order_] \:6298\:308a\:7d19\:30b0\:30e9\:30d5G\:306e\:8868\:793a.
\:305f\:3060\:3057,width\:306f\:30ec\:30a4\:30e4\:30fc\:9593\:306e\:5e45\:306e\:9577\:3055,Moji\:306f\:9762\:306eID\:8868\:793a\:306e\:771f\:507d,order\:306f\:4e0a\:4e0b\:3069\:3061\:3089\:306b\:3064\:3081\:3066\:8868\:793a\:304b\:771f\:507d
(\:30c7\:30d5\:30a9\:30eb\:30c8\:306fTrue\:3067\:9802\:4e0a\:304b\:3089).";


(*EquivalentDivision\:306e\:307f\:9069\:7528*)
GOutput3D02old[G_,width_,Moji_]:=Module[{Ans={  Graphics3D[{},Boxed->False]  },
i,Zcount=10,Kg,Kg2,RestKey,FGraphics3D,G00,Key,ZCoordinate,PiE},

(*\:30b0\:30e9\:30d5G00\:306e\:9762Key\:3092\:9ad8\:3055ZCoordinate\:306b\:8868\:793a*)
FGraphics3D[G00_,Key_,ZCoordinate_]:=Module[{gCoordinate},
gCoordinate=Map[Append[#,ZCoordinate]&,FCoordinate[G00,Key]];
If[Moji,
Graphics3D[{FaceForm[Yellow,Green],Polygon[gCoordinate]
,Text[Style[Subscript["f", (Key)],Large,Bold,Black],(Total[gCoordinate]/Length[gCoordinate])]}
,Boxed->False] 
,(*False\:306e\:3068\:304d*)
Graphics3D[{FaceForm[Yellow,Green],Polygon[gCoordinate]}
,Boxed->False] 
]
];(*\[UpArrow]FGraphics3D\:5b9a\:7fa9*)


RestKey=Keys[G["F"]];(*\:63cf\:304b\:308c\:3066\:3044\:306a\:3044\:9762\:306e\:30ad\:30fc*)
PiE=EquivalentDivision[RestKey,G];(*\:540c\:5024\:985e\:306e\:30ad\:30fc*)
Kg=Peak[RestKey,G["S"]];(*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)

While[Kg!= {},
For[i=1,i<=Length[Kg],i++,
Kg2=Kg[[i]];Kg2=Select[PiE,(MemberQ[#,Kg2]&)(*Kg\:3092\:542b\:3080PiE\:306e\:90e8\:5206\:3092\:62bd\:51fa*)][[1]];(*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
(*\:30d4\:30fc\:30af\:306e\:9762\:3092\:8868\:793a*)
Ans=Join[Ans,Map[FGraphics3D[G,#,Zcount]&,Kg2]];
RestKey=Complement[RestKey,Kg2];(*\:88dc\:96c6\:5408*)
Zcount=Zcount-width;
];
Kg=Peak[RestKey,G["S"]];(*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)


];(*While_end*)

Show[Ans]
];






(* Pi=Keys[G["F"]]; *)
EquivalentDivision[PiKeys_,G_]:=Module[{PiE,fKey,Ans,G0=G,F0,A0},

If[PiKeys== {},Return[{}],(*\:7a7a\:306a\:3089\:7d42\:4e86*)
fKey=First[PiKeys];
Ans=EDivision[{fKey},{},Complement[PiKeys,{fKey}],G0];(*f\:306e\:540c\:5024\:985e*)
(*\[DownArrow]\:518d\:5e30\:547c\:3073\:51fa\:3057,\:540c\:5024\:985e\:306e\:96c6\:5408{Ans1,Ans2,Ans3,...}*)
PiE=Union[{Ans},EquivalentDivision[Complement[PiKeys,Ans],G0]];
Return[ PiE ]
]
];

(*\:88dc\:52a9\:95a2\:6570*)
EDivision[U_,R_,W_,G_]:=Module[{fKey,gKey,i,V={},G0=G,F0,A0},
F0=G0["F"];A0=G0["A"];
If[U== {},Return[R],(*\:7a7a\:306a\:3089\:7d42\:4e86*)
fKey=First[U];
For[i=1,i<=Length[W],i++,
gKey=W[[i]];
If[(ClockWise[F0[fKey]]==ClockWise[F0[gKey]])&&( MemberQ[A0[fKey], gKey] ),(*\:9762\:306e\:8868\:88cf&\:96a3\:63a5*)
V=Join[V,{gKey}] ];
];(*For_end*)

Return[EDivision[ Complement[Union[U,V],{fKey}] , Union[R,{fKey}] , Complement[W,V] , G0 ]]
]
];


EquivalentDivision::usage="EquivalentDivision[PiKeys_,G_] 
 \:9762\:306eID\:96c6\:5408PiKeys\:3092\:96a3\:63a5\:95a2\:4fc2\:540c\:5024\:985e\:306e\:96c6\:5408\:306b\:5206\:5272\:3059\:308b.";


LayerGraph[PiE_,G_]:=Module[{G0=G,i,V,E,L,a,Rep,S0},
V={};(*\:540c\:5024\:985e\:306e\:4ee3\:8868\:5143\:306eID\:96c6\:5408*)
E={};(*\:4ee3\:8868\:5143\:306b\:7f6e\:63db\:3057\:305f\:91cd\:7573\:95a2\:4fc2*)
Rep={};

For[i=1,i<=Length[PiE],i++,
L=PiE[[i]];a=First[L];
V=Join[V,{a}];(*\:540c\:5024\:985e\:306e\:4ee3\:8868\:5143\:306eID\:96c6\:5408*)

Rep=Join[Rep,Map[(#->a)&,L]];
];(*For_end*)

S0=G0["S"];
E=S0/.Rep;
E=DeleteDuplicates[E];

{V,E} ];(*LayerGraph_end*)


(*\:30ec\:30a4\:30e4\:30fc\:8868\:793a\:9806\:5e8f*)
LayerOrder[{V_,E_}]:=LayerOrder[{V,E},True];
LayerOrder[{V_,E_},order_]:=Module[{A,B,R,DL={}},

If[V=={},Return[{}] ];(*\:518d\:5e30\:7d42\:4e86*)
A=V;(*\:540c\:5024\:985e\:306e\:4ee3\:8868\:5143\:306eID\:96c6\:5408*)
B=E;(*\:4ee3\:8868\:5143\:306b\:7f6e\:63db\:3057\:305f\:91cd\:7573\:95a2\:4fc2*)
If[order, (*\:771f\:306a\:3089\:9802\:4e0a\:304b\:3089*)R=Peak[A , B] ,(*\:507d\:306a\:3089\:5e95\:304b\:3089*)R=Abyss[A , B]];

If[R=={},Print["Cyclic layer graph"];Return[{}] ,
A=Complement[A,R];(*\:88dc\:96c6\:5408*)
DL=Join[{R},LayerOrder[{A,B},order]];(*\:518d\:5e30\:547c\:3073\:51fa\:3057*)

Return[DL]
];
 ];(*LayerOrder_end*)


LayerGraph::usage="LayerGraph[PiE_,G_] \:540c\:5024\:985e\:5206\:5272PiE\:304b\:3089,{V,E} \:3092\:8fd4\:3059.
\:305f\:3060\:3057,V\:306f\:4ee3\:8868\:5143\:306eID\:96c6\:5408,E\:306f\:4ee3\:8868\:5143\:306b\:7f6e\:63db\:3057\:305f\:91cd\:7573\:95a2\:4fc2\:3067\:3042\:308b.";
LayerOrder::usage="LayerOrder[{V_,E_},order_] \:4ee3\:8868\:5143\:96c6\:5408V\:3068\:7f6e\:63db\:91cd\:7573\:95a2\:4fc2E\:304b\:3089,\:30ec\:30a4\:30e4\:30fc\:8868\:793a\:9806\:5e8fD\:3092\:8fd4\:3059.
\:305f\:3060\:3057,order\:304c\:771f\:306a\:3089\:9802\:4e0a\:304b\:3089,order\:304c\:507d\:306a\:3089\:5e95\:304b\:3089\:8868\:793a\:3059\:308b.";


ClockWise[f_]:=Module[{Ans},
Ans=Det[{ f[[2]]-f[[1]] , f[[3]]-f[[1]] }];


If[Ans<0,Return[-1],Return[1]]
];


ClockWise::usage="ClockWise[f_] \:9762f\:304c\:6642\:8a08\:56de\:308a\:306a\:3089\:300c-1\:300d , \:53cd\:6642\:8a08\:56de\:308a\:306a\:3089\:300c1\:300d\:3092\:8fd4\:3059.";


(* ::Text:: *)
(*GOutput3D03*)


(*\:3064\:306a\:304e\:3092\:8ffd\:52a0,\:30a4\:30f3\:30d7\:30c3\:30c8\:3092\:30aa\:30d7\:30b7\:30e7\:30f3\:7684\:306b\:5909\:66f4*)
GOutput3D03[G_]:=GOutput3D03[G,{}];
GOutput3D03[G_,Op_,opts:OptionsPattern[]]:=Module[{Ans={  Graphics3D[{},Boxed->False,opts]  },
OpAssoc,width,Moji,order,Hinge,HColor,HOpacity,FoldLine,
FGraphics3D,FMid3D,HingeID={},H0,i1,i2,z1,z2,i,Zcount=10,LO,Kg,PiE,Fz=<||>},
Print["GOutput3D03"];
(*\[DownArrow]\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)
OpAssoc=Association[{"width"->1,"Moji"->True,"order"->True,"FoldLine"-> False,
"Hinge"->False,"HColor"->Gray,"HOpacity"->0.5}];(*\:30c7\:30d5\:30a9\:30eb\:30c8\:306e\:5024*)
AssociateTo[OpAssoc, Op];
width=OpAssoc["width"];
Moji=OpAssoc["Moji"];
order=OpAssoc["order"];
Hinge=OpAssoc["Hinge"];
HColor=OpAssoc["HColor"];
HOpacity=OpAssoc["HOpacity"];
FoldLine=OpAssoc["FoldLine"];
(*\[UpArrow]\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)



FMid3D[G00_,fKey_]:=Append[(Total[(G00["F"][fKey])]/Length[(G00["F"][fKey])]) , Fz[fKey]];

(*\:30b0\:30e9\:30d5G00\:306e\:9762Key\:3092\:9ad8\:3055ZCoordinate\:306b\:8868\:793a*)
FGraphics3D[G00_,fKey_]:=Module[{f3D},
f3D=Map[Append[#,Fz[fKey]]&,FCoordinate[G00,fKey]];
If[Moji,
Graphics3D[{FaceForm[Yellow,Green],Polygon[f3D]
,Text[Style[Subscript["f", (fKey)],Large,Bold,Black],(Total[f3D]/Length[f3D])]}
,Boxed->False,opts
]
,(*False\:306e\:3068\:304d*)
Graphics3D[{FaceForm[Yellow,Green],Polygon[f3D]}
,Boxed->False,opts]
](*If_end*)
];(*\[UpArrow]FGraphics3D\:5b9a\:7fa9*)


(*\[DownArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)
PiE=EquivalentDivision[Keys[G["F"]],G];(*\:540c\:5024\:985e\:306e\:30ad\:30fc*)
LO=LayerOrder[LayerGraph[PiE,G],order];(*\:9806*)

While[LO!= {},
i=First[LO];
Kg=Flatten[Table[
Select[PiE,(MemberQ[#,j]&)(*i\:3092\:542b\:3080PiE\:306e\:90e8\:5206\:3092\:62bd\:51fa*)][[1]](*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
,{j,i}]];(*\:540c\:3058\:540c\:5024\:985e\:306f\:307e\:3068\:3081\:3066\:8868\:793a*)
(* Z\:5ea7\:6a19\:3092\:8868\:793a*)
AssociateTo[Fz,Map[(#->Zcount)&,Kg] ];

(*\:3064\:306a\:304e*)Table[
HingeID=Union[HingeID,(Map[Sort[{fKey,#}]&,Complement[G["A"][fKey],Append[Kg,0]]])] ,{fKey,Kg}];

LO=Rest[LO];
Zcount=Zcount-width;
];(*While_end*)
(*\[UpArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)

Ans=Map[FGraphics3D[G,#]&,Keys[G["F"]]];
(*\:3064\:306a\:304e\:8ffd\:52a0\[DownArrow]*)
If[Hinge,While[HingeID!= {},
i=First[HingeID];
H0=Intersection[G["F"][i[[1]]],G["F"][i[[2]]]];
i1=H0[[1]]; i2=H0[[2]];
z1=Fz[i[[1]]];z2=Fz[i[[2]]];
H0={Append[i1,z1],Append[i2,z1],Append[i2,(z1+z2)/2],Append[i2,z2],Append[i1,z2]};
Ans=Join[Ans,{
Graphics3D[{HColor,EdgeForm[{Dashed}](*\:3075\:3061*),Opacity[HOpacity](*\:900f\:660e\:5ea6*),Polygon[H0]}]
}];
HingeID=Rest[HingeID];
](*While_end*)];
(*\:3064\:306a\:304e\:8ffd\:52a0\[UpArrow]*)

Show[Ans]
];


GOutput3D03::usage="GOutput3D03[G_,Op_] \:6298\:308a\:7d19\:30b0\:30e9\:30d5G\:306e\:8868\:793a.
\:305f\:3060\:3057,Op\:3067\:30aa\:30d7\:30b7\:30e7\:30f3\:306e\:5909\:66f4\:53ef\:80fd\:3002
width\:306f\:30ec\:30a4\:30e4\:30fc\:9593\:306e\:5e45\:306e\:9577\:3055,Moji\:306f\:9762\:306eID\:8868\:793a\:306e\:771f\:507d,
order\:306f\:4e0a\:4e0b\:3069\:3061\:3089\:306b\:3064\:3081\:3066\:8868\:793a\:304b\:771f\:507d(\:30c7\:30d5\:30a9\:30eb\:30c8\:306fTrue\:3067\:9802\:4e0a\:304b\:3089).
Hinge\:306f\:3064\:306a\:304e\:8868\:793a\:306e\:771f\:507d,HColor\:306f\:3064\:306a\:304e\:306e\:8272,HOpacity\:306f\:3064\:306a\:304e\:306e\:900f\:660e\:5ea6(0~1).
\:30c7\:30d5\:30a9\:30eb\:30c8\:306fOp={\"width\" \[Rule]1,\"Moji\"\[Rule]True,\"order\"\[Rule]True,\"Hinge\"\[Rule]False,\"HColor\"\[Rule]Gray,\"HOpacity\"\[Rule]0.5}
.";


(*\:3064\:306a\:304e\:3092\:8ffd\:52a0,\:30a4\:30f3\:30d7\:30c3\:30c8\:3092\:30aa\:30d7\:30b7\:30e7\:30f3\:7684\:306b\:5909\:66f4*)
(*\:3064\:306a\:304e\:304c\:5171\:901a\:90e8\:5206\:3068\:3063\:3066\:3044\:308b\:304b\:3089\:3001\:5909\:306a\:5834\:6240\:306b*)
GOutput3D03old[G_]:=GOutput3D03old[G,{}];
GOutput3D03old[G_,Op_,opts:OptionsPattern[]]:=Module[{Ans={  Graphics3D[{},Boxed->False,opts]  },
OpAssoc,width,Moji,order,Hinge,HColor,HOpacity,
FGraphics3D,FMid3D,HingeID={},H0,i1,i2,z1,z2,i,Zcount=10,LO,Kg,PiE,Fz=<||>},
Print["GOutput3D03"];
(*\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)
OpAssoc=Association[{"width"->1,"Moji"->True,"order"->True,
"Hinge"->True,"HColor"->Gray,"HOpacity"->0.5}];(*\:30c7\:30d5\:30a9\:30eb\:30c8\:306e\:5024*)
AssociateTo[OpAssoc, Op];
width=OpAssoc["width"];
Moji=OpAssoc["Moji"];
order=OpAssoc["order"];
Hinge=OpAssoc["Hinge"];
HColor=OpAssoc["HColor"];
HOpacity=OpAssoc["HOpacity"];
(*\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)

FMid3D[G00_,fKey_]:=Append[(Total[(G00["F"][fKey])]/Length[(G00["F"][fKey])]) , Fz[fKey]];

(*\:30b0\:30e9\:30d5G00\:306e\:9762Key\:3092\:9ad8\:3055ZCoordinate\:306b\:8868\:793a*)
FGraphics3D[G00_,fKey_]:=Module[{f3D},
f3D=Map[Append[#,Fz[fKey]]&,FCoordinate[G00,fKey]];
If[Moji,
Graphics3D[{FaceForm[Yellow,Green],Polygon[f3D]
,Text[Style[Subscript["f", (fKey)],Large,Bold,Black],(Total[f3D]/Length[f3D])]}
,Boxed->False,opts
]
,(*False\:306e\:3068\:304d*)
Graphics3D[{FaceForm[Yellow,Green],Polygon[f3D]}
,Boxed->False,opts]
](*If_end*)
];(*\[UpArrow]FGraphics3D\:5b9a\:7fa9*)


(*\[DownArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)
PiE=EquivalentDivision[Keys[G["F"]],G];(*\:540c\:5024\:985e\:306e\:30ad\:30fc*)
LO=LayerOrder[LayerGraph[PiE,G],order];(*\:9806*)

While[LO!= {},
i=First[LO];
Kg=Flatten[Table[
Select[PiE,(MemberQ[#,j]&)(*i\:3092\:542b\:3080PiE\:306e\:90e8\:5206\:3092\:62bd\:51fa*)][[1]](*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
,{j,i}]];(*\:540c\:3058\:540c\:5024\:985e\:306f\:307e\:3068\:3081\:3066\:8868\:793a*)
(* Z\:5ea7\:6a19\:3092\:8868\:793a*)
AssociateTo[Fz,Map[(#->Zcount)&,Kg] ];

(*\:3064\:306a\:304e*)Table[
HingeID=Union[HingeID,(Map[Sort[{fKey,#}]&,Complement[G["A"][fKey],Append[Kg,0]]])] ,{fKey,Kg}];

LO=Rest[LO];
Zcount=Zcount-width;
];(*While_end*)
(*\[UpArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)

Ans=Map[FGraphics3D[G,#]&,Keys[G["F"]]];
(*\:3064\:306a\:304e\:8ffd\:52a0\[DownArrow]*)
If[Hinge,While[HingeID!= {},
i=First[HingeID];
H0=Intersection[G["F"][i[[1]]],G["F"][i[[2]]]];
i1=H0[[1]]; i2=H0[[2]];
z1=Fz[i[[1]]];z2=Fz[i[[2]]];
H0={Append[i1,z1],Append[i2,z1],Append[i2,(z1+z2)/2],Append[i2,z2],Append[i1,z2]};
Ans=Join[Ans,{
Graphics3D[{HColor,EdgeForm[{Dashed}](*\:3075\:3061*),Opacity[HOpacity](*\:900f\:660e\:5ea6*),Polygon[H0]}]
}];
HingeID=Rest[HingeID];
];(*While_end*)];
(*\:3064\:306a\:304e\:8ffd\:52a0\[UpArrow]*)

Show[Ans]
];




(* ::Text:: *)
(*GOutput2D*)


GOutput2D[G_]:=GOutput2D[G,{}];
GOutput2D[G_,Op_,opts:OptionsPattern[]]:=DynamicModule[{Ans={  },Ans2={  },
OpAssoc,Moji,order,Pnt,m0,x,y,mL,mCol,
PntList,Cfront,Cback,Col=Yellow,TabV,LabT,
FGraphics2D,H0,i1,i2,z1,z2,i,Zcount=0,LO,Kg,PiE,Fz=<||>},
Print["GOutput2D"];
(*\[DownArrow]\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)
OpAssoc=Association[{"Moji"->False,"order"->False,"Pnt"->True,
"Cfront"->Yellow,"Cback"->Green,"Tab"->True,"Label"->True,"m"->0,"mCol"->{Blue,Pink,Purple} }];(*\:30c7\:30d5\:30a9\:30eb\:30c8\:306e\:5024*)
AssociateTo[OpAssoc, Op];
Moji=OpAssoc["Moji"];
order=OpAssoc["order"];
Pnt=OpAssoc["Pnt"];
Cfront=OpAssoc["Cfront"];
Cback=OpAssoc["Cback"];
TabV=OpAssoc["Tab"];
LabT=OpAssoc["Label"];
m0=OpAssoc["m"];
mCol=OpAssoc["mCol"];
(*\[UpArrow]\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)


(*\:30b0\:30e9\:30d5G00\:306e\:9762Key\:3092\:8868\:793a*)
FGraphics2D[G00_,fKey_]:=Module[{f2D},
f2D=FCoordinate[G00,fKey];
If[ClockWise[f2D]==-1,Col=Cback,Col=Cfront];
If[Moji,
Graphics[{Col,EdgeForm[Thick],Polygon[f2D]
,Text[Style[Subscript["f", (fKey)],Large,Bold,Black],(Total[f2D]/Length[f2D])]
}
,opts
]
,(*False\:306e\:3068\:304d*)
If[LabT,
Graphics[Tooltip[ {Col,EdgeForm[Thick],Polygon[f2D]}
,Subscript["f", (fKey)]] ,opts]
,(*False\:306e\:3068\:304d*)
Graphics[ {Col,EdgeForm[Thick],Polygon[f2D]} ,opts] ]
](*If_end*)
];(*\[UpArrow]FGraphics2D\:5b9a\:7fa9*)

(*\[DownArrow]\:70b9\:306e\:8ffd\:52a01*)
PntList=Union[ Flatten[Values[ G["F"] ],1] ];(*{x,y}\:306e\:5f62\:3092\:4fdd\:3064\:70ba,Flat\:306f1\:30ec\:30d9\:30eb*)
(*\[UpArrow]\:70b9\:306e\:8ffd\:52a01*)

(*\[DownArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)
PiE=EquivalentDivision[Keys[G["F"]],G];(*\:540c\:5024\:985e\:306e\:30ad\:30fc*)
LO=LayerOrder[LayerGraph[PiE,G],order];(*\:9806*)

While[LO!= {},
i=First[LO];
Kg=Flatten[Table[
Select[PiE,(MemberQ[#,j]&)(*i\:3092\:542b\:3080PiE\:306e\:90e8\:5206\:3092\:62bd\:51fa*)][[1]](*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
,{j,i}]];(*\:540c\:3058\:540c\:5024\:985e\:306f\:307e\:3068\:3081\:3066\:8868\:793a*)
(* Z\:5ea7\:6a19\:3092\:8868\:793a*)
AssociateTo[Fz,Map[(#->Zcount)&,Kg] ];

If[LabT,
Ans=Append[Ans,
Show[Join[( Map[FGraphics2D[G,#]&,Kg] ) , Map[ (Graphics[Tooltip[{PointSize[Large],Red,Point[#]},#],opts])& ,PntList] ]]
],(*\:507d*)
Ans=Append[Ans,
Show[Join[( Map[FGraphics2D[G,#]&,Kg] ) , Map[ (Graphics[{PointSize[Large],Red,Point[#]},opts])& ,PntList] ]]
]
];
(*\[UpArrow]\:30b0\:30e9\:30d5\:30a3\:30c3\:30af\:30b9\:6c7a\:3081\:308b*)

LO=Rest[LO];
Zcount=Zcount-1;
];(*While_end*)
(*\[UpArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)


(*\[DownArrow]\:70b9\:306e\:8ffd\:52a02*)
If[LabT,
Ans2=Join[Ans,Map[ (Graphics[Tooltip[{PointSize[Large],Red,Point[#]},#],opts])& ,PntList] ]
,(*False\:306e\:3068\:304d*)
Ans2=Join[Ans,Map[ (Graphics[{PointSize[Large],Red,Point[#]},opts])& ,PntList] ]
];
(*\[UpArrow]\:70b9\:306e\:8ffd\:52a02*)

(*\[DownArrow]\:6298\:308a\:7dda\:306e\:8ffd\:52a0:\:9078\:629e*)
If[m0==0,(*\:771f*)(*Print["A"]*),(*\:507d*)(*Print["B"]*),(*\:4ed6*)(*Print["C"];*)
mL=Flatten[{m0[{x,y}]}];
Print["Line1=",mCol[[1]]," ;Line2=",mCol[[2]]," ;Line3=",mCol[[3]]];(*--Print--*)
Ans2=Join[Ans2,
Table[(ContourPlot[mL[[j]]==0,{x,-1,11},{y,-1,11},ContourStyle->mCol[[j]]]) ,{j,Length[mL]}] ]

];
(*\[UpArrow]\:6298\:308a\:7dda\:306e\:8ffd\:52a0:\:9078\:629e*)

(*\[DownArrow]\:30bf\:30d6*)
If[TabV,
{TabView[Ans],Show[Ans2]}
,Show[Ans2] ]


];


GOutput2D::usage="GOutput2D[G_,Op_] \:6298\:308a\:7d19\:30b0\:30e9\:30d5G\:306e\:8868\:793a.
\:305f\:3060\:3057,Op\:3067\:30aa\:30d7\:30b7\:30e7\:30f3\:306e\:5909\:66f4\:53ef\:80fd\:3002
Moji\:306f\:9762\:306eID\:8868\:793a\:306e\:771f\:507d,order\:306f\:4e0a\:4e0b\:3069\:3061\:3089\:306b\:3064\:3081\:3066\:8868\:793a\:304b\:771f\:507d(\:30c7\:30d5\:30a9\:30eb\:30c8\:306fFalse\:3067\:5e95\:304b\:3089).
Cfront\:306f\:8868\:306e\:8272,Cback\:306f\:88cf\:306e\:8272,Tab\:306f\:30ec\:30a4\:30e4\:30fc\:306e\:30bf\:30d6\:8868\:793a\:306eOnOff.
\:30c7\:30d5\:30a9\:30eb\:30c8\:306fOp={\"Moji\"\[Rule]True,\"order\"\[Rule]True,\"Cfront\"\[Rule]Yellow,\"Cback\"\[Rule]Green,\"Tab\"\[Rule] True}
.";


(* ::Text:: *)
(*GOutput2D02*)


GOutput2D02[G_]:=GOutput2D02[G,{}];
GOutput2D02[G_,Op_,opts:OptionsPattern[]]:=DynamicModule[{Ans={  },Ans2={  },
OpAssoc,Moji,order,Pnt,m0,x,y,mL,mCol,
PntList,Cfront,Cback,Col=Yellow,TabV,LabT,
FGraphics2D,H0,i1,i2,z1,z2,i,Zcount=0,LO,Kg,PiE,Fz=<||>},
Print["GOutput2D"];
(*\[DownArrow]\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)
OpAssoc=Association[{"Moji"->False,"order"->False,"Pnt"->True,
"Cfront"->Yellow,"Cback"->Green,"Tab"->True,"Label"->True,"m"->0,"mCol"->{Blue,Pink,Purple} }];(*\:30c7\:30d5\:30a9\:30eb\:30c8\:306e\:5024*)
AssociateTo[OpAssoc, Op];
Moji=OpAssoc["Moji"];
order=OpAssoc["order"];
Pnt=OpAssoc["Pnt"];
Cfront=OpAssoc["Cfront"];
Cback=OpAssoc["Cback"];
TabV=OpAssoc["Tab"];
LabT=OpAssoc["Label"];
m0=OpAssoc["m"];
mCol=OpAssoc["mCol"];
(*\[UpArrow]\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)


(*\:30b0\:30e9\:30d5G00\:306e\:9762Key\:3092\:8868\:793a*)
FGraphics2D[G00_,fKey_]:=Module[{f2D},
f2D=FCoordinate[G00,fKey];
If[ClockWise[f2D]==-1,Col=Cback,Col=Cfront];
If[Moji,
Graphics[{Col,EdgeForm[Thick],Polygon[f2D]
,Text[Style[Subscript["f", (fKey)],Large,Bold,Black],(Total[f2D]/Length[f2D])]
,Graphics[{PointSize[Large],Red,Point[f2D]},opts]
}
,opts
]
,(*False\:306e\:3068\:304d*)
If[LabT,
Graphics[Tooltip[ {Col,EdgeForm[Thick],Polygon[f2D]}
,Subscript["f", (fKey)]] ,opts]
,(*False\:306e\:3068\:304d*)
Graphics[ {Col,EdgeForm[Thick],Polygon[f2D]} ,opts] ]
](*If_end*)
];(*\[UpArrow]FGraphics2D\:5b9a\:7fa9*)

(*\[DownArrow]\:70b9\:306e\:8ffd\:52a01*)
PntList=Union[ Flatten[Values[ G["F"] ],1] ];(*{x,y}\:306e\:5f62\:3092\:4fdd\:3064\:70ba,Flat\:306f1\:30ec\:30d9\:30eb*)
(*\[UpArrow]\:70b9\:306e\:8ffd\:52a01*)

(*\[DownArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)
PiE=EquivalentDivision[Keys[G["F"]],G];(*\:540c\:5024\:985e\:306e\:30ad\:30fc*)
LO=LayerOrder[LayerGraph[PiE,G],order];(*\:9806*)

While[LO!= {},
i=First[LO];
Kg=Flatten[Table[
Select[PiE,(MemberQ[#,j]&)(*i\:3092\:542b\:3080PiE\:306e\:90e8\:5206\:3092\:62bd\:51fa*)][[1]](*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
,{j,i}]];(*\:540c\:3058\:540c\:5024\:985e\:306f\:307e\:3068\:3081\:3066\:8868\:793a*)
(* Z\:5ea7\:6a19\:3092\:8868\:793a*)
AssociateTo[Fz,Map[(#->Zcount)&,Kg] ];

Ans=Append[Ans,
Show[( Map[FGraphics2D[G,#]&,Kg] ) ]];

LO=Rest[LO];
Zcount=Zcount-1;
];(*While_end*)
(*\[UpArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)


Ans2=Ans;

(*\[DownArrow]\:6298\:308a\:7dda\:306e\:8ffd\:52a0*)
If[m0==0,(*\:771f*)Print["A"],(*\:507d*)Print["B"],(*\:4ed6*)Print["C"];
mL=Flatten[{m0[{x,y}]}];
Print["Line1=",mCol[[1]]," ;Line2=",mCol[[2]]," ;Line3=",mCol[[3]]];(*--Print--*)
Ans2=Join[Ans2,
Table[(ContourPlot[mL[[j]]==0,{x,-1,11},{y,-1,11},ContourStyle->mCol[[j]]]) ,{j,Length[mL]}] ]

];
(*\[UpArrow]\:6298\:308a\:7dda\:306e\:8ffd\:52a0*)

(*\[DownArrow]\:30bf\:30d6*)
If[TabV,
{TabView[Ans],Show[Ans2]}
,Show[Ans2] ]


];


(* ::Text:: *)
(*GMOutput3D*)


GMOutput3D[G_,N_]:=GMOutput3D[G,N,{}];
GMOutput3D[G_,N_,Op_,opts:OptionsPattern[]]:=Module[{Ans={  Graphics3D[{},Boxed->False,opts]  },
OpAssoc,width,Moji,order,Hinge,HColor,HOpacity,
FGraphics3D2,FMid3D,G0,GM,a,H0,i1,i2,z1,z2,i,Zcount=10,LO,Kg,PiE,Fz=<||>,G2,Fz2=<||>},
Print["GMOutput3D"];
(*\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)
OpAssoc=Association[{"width"->1,"Moji"->True,"order"->True}];(*\:30c7\:30d5\:30a9\:30eb\:30c8\:306e\:5024*)
AssociateTo[OpAssoc, Op];
width=OpAssoc["width"];
Moji=OpAssoc["Moji"];
order=OpAssoc["order"];
(*\:30aa\:30d7\:30b7\:30e7\:30f3\:8a2d\:5b9a*)

FMid3D[G00_,fKey_]:=Append[(Total[(G00["F"][fKey])]/Length[(G00["F"][fKey])]) , Fz[fKey]];


(*\:30b0\:30e9\:30d5G00\:306e\:9762Key\:3092\:9ad8\:3055ZCoordinate\:306b\:8868\:793a*)
FGraphics3D2[GM0_,a0_,fKey_]:=Module[{f3D,F00,Z0},
F00=GM0[a0];Z0=If[Abs[a0]>= \[Pi]/2,Fz[fKey],Fz2[fKey]];
f3D=Map[#+{0,0,Z0}&,F00[fKey]];
If[Moji,
Graphics3D[{FaceForm[Yellow,Green],Polygon[f3D]
,Text[Style[Subscript["f", (fKey)],Large,Bold,Black],(Total[f3D]/Length[f3D])]}
,Boxed->False,opts
]
,(*False\:306e\:3068\:304d*)
Graphics3D[{FaceForm[Yellow,Green],Polygon[f3D]}
,Boxed->False,opts]
](*If_end*)
];(*\[UpArrow]FGraphics3D\:5b9a\:7fa9*)

(*\[DownArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)
G0=G;Zcount=10;
PiE=EquivalentDivision[Keys[G0["F"]],G0];(*\:540c\:5024\:985e\:306e\:30ad\:30fc*)
LO=LayerOrder[LayerGraph[PiE,G0],order];(*\:9806*)

While[LO!= {},
i=First[LO];
Kg=Flatten[Table[
Select[PiE,(MemberQ[#,j]&)(*i\:3092\:542b\:3080PiE\:306e\:90e8\:5206\:3092\:62bd\:51fa*)][[1]](*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
,{j,i}]];(*\:540c\:3058\:540c\:5024\:985e\:306f\:307e\:3068\:3081\:3066\:8868\:793a*)
(* Z\:5ea7\:6a19\:3092\:8868\:793a*)
AssociateTo[Fz,Map[(#->Zcount)&,Kg] ];

LO=Rest[LO];
Zcount=Zcount-width;
];(*While_end*)
(*\[UpArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b*)

(*\[DownArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b2*)
G2=OriBack[G];Zcount=10;
PiE=EquivalentDivision[Keys[G2["F"]],G2];(*\:540c\:5024\:985e\:306e\:30ad\:30fc*)
LO=LayerOrder[LayerGraph[PiE,G2],order];(*\:9806*)

While[LO!= {},
i=First[LO];
Kg=Flatten[Table[
Select[PiE,(MemberQ[#,j]&)(*i\:3092\:542b\:3080PiE\:306e\:90e8\:5206\:3092\:62bd\:51fa*)][[1]](*\:30d4\:30fc\:30af\:306e\:96c6\:5408*)
,{j,i}]];(*\:540c\:3058\:540c\:5024\:985e\:306f\:307e\:3068\:3081\:3066\:8868\:793a*)
(* Z\:5ea7\:6a19\:3092\:8868\:793a*)
AssociateTo[Fz2,Map[(#->Zcount)&,Kg] ];

LO=Rest[LO];
Zcount=Zcount-width;
];(*While_end*)
(*\[UpArrow]z\:5ea7\:6a19\:6c7a\:3081\:308b2*)

GM=OriMovie[G,N];
Table[Show[Map[FGraphics3D2[GM,a,#]&,(Keys[GM[a]])]],{a,Keys[GM]}]
];


OriMovie[G_,N_]:=Module[{Ans=<||>,i,j,k,FKeys,G1,G2=G,Fm,Fi,fj,F1,F2,P1,P2,Pm,r,a},
F2=G2["F"];
G1=OriBack[G,1];
F1=G1["F"];


For[k=0,k<=Abs[N],k++,
a=(k/N)*\[Pi];

Fm=<||>;FKeys=Keys[F2];
While[FKeys!={},i=First[FKeys];

Fi={};
For[j=1,j<=Length[F1[i]],j++,
P1=F1[i][[j]];P2=F2[i][[j]];
If[P1==P2,fj=Append[P1 ,0 ],
Pm=(P1+P2)/2;(*\:4e2d\:70b9*)
r=Norm[(P2-P1)]/2;(*\:9577\:3055*)
fj=Append[(Pm+(Cos[a]/2)*(P1-P2)) , r*Sin[a] ]
];(*If_end*)
Fi=Append[Fi,fj];
];(*For_end*)
AssociateTo[Fm,i->Fi];

FKeys=Rest[FKeys];];(*While_end*)

AssociateTo[Ans,a->Fm];];(*For_end*)

Return[Ans];
];


(* ::Text:: *)
(*C\:3084Pi_M \:3092\:751f\:6210\:3059\:308b.*)


(* ::Text:: *)
(*TransitiveR*)


TransitiveR[G_,A_,R_,k_]:=Module[{Ans=A,LookAns=A,Rest,W,f},

Rest=Complement[Keys[G["F"]],LookAns];
If[k>=0,W[f_]:=Select[Rest,JudgeR[G,R,#,f]&]];
If[k<0,W[f_]:=Select[Rest,JudgeR[G,R,f,#]&]];

While[LookAns!= {},
LookAns=Union[Flatten[Map[W[#]&,LookAns]]];
Rest=Complement[Rest,LookAns];
Ans=Union[Ans,LookAns];
];(*While_end*)
Ans
];

TransitiveR[G_,A_,R_,k_,m_]:=Module[{Ans=A,LookAns=A,Rest,W,f},

Rest=Complement[Keys[G["F"]],LookAns];
If[k>=0,W[f_]:=Select[Rest,JudgeR[G,R,#,f,m]&]];
If[k<0,W[f_]:=Select[Rest,JudgeR[G,R,f,#,m]&]];

While[LookAns!= {},
LookAns=Union[Flatten[Map[W[#]&,LookAns]]];
Rest=Complement[Rest,LookAns];
Ans=Union[Ans,LookAns];
];(*While_end*)
Ans
];


(* ::Text:: *)
(*JudgeR*)


JudgeR[G_,R_,x_,y_]:=Module[{m,Q,Ans},
If[R=="A",Return[MemberQ[G[R][x],y]]];
If[R=="S",Return[MemberQ[G[R],{x,y}]]];
If[R=="EDivision",Return[ClockWise[G["F"][x]]==ClockWise[G["F"][y]]&&JudgeR[G,"A",x,y]]];
If[R=="Overlap",Return[OverLapJudge[G["F"][x],G["F"][y]]]];
Return[False]
];


JudgeR[G_,R_,x_,y_,m_]:=Module[{Q,Ans},
If[R=="LA" && JudgeR[G,"A",x,y],
Q=ShareVertex[G,x,y];
Ans=Map[SignQ[m,#]<=0&,Q];
Ans=Ans[[1]]&&Ans[[2]];
Return[Ans]
];
If[R=="NLA",Return[JudgeR[G,"A",x,y]&&(!JudgeR[G,"LA",x,y,m])]];
If[R=="NLAS",Return[JudgeR[G,"NLA",x,y,m]||JudgeR[G,"S",x,y]]];
Return[JudgeR[G,R,x,y]]
];






ShareVertex[G_,x_,y_]:=
{G["F"][x][[Mod[Position[G["A"][x],y][[1,1]]-1,Length[G["A"][x]],1]]]
,G["F"][x][[Position[G["A"][x],y][[1,1]]]]};


(* ::Text:: *)
(*DivideFace, RoteFace*)


DivideFace[G_,Ic_,m_]:=TransitiveR[G,Ic,"NLA",0,m];
RoteFace[G_,C_,m_,\[Theta]_]:=TransitiveR[G,C,"NLAS",\[Theta],m];


(* ::Text:: *)
(*Oriable*)


Oriable[G_,PiM_,m_]:=Module[{P,B},
P=Union[Flatten[Map[FCoordinate[G,#]&,PiM],1]];
B=Map[SignQ[m,#]>=0&,P];
Return[!MemberQ[B,False]]
];


(* ::Text:: *)
(*Ori*)


FirstG := <|"F"-><|1->{{0.,0.},{10.,0.},{10.,10.},{0.,10.}}|>,"A"-><|1->{0,0,0,0}|>,"S"->{}
,"step"-> 0,"mList"-> <||>,"PiMList"-> <||>,"ThList"-> <||> |>;
FirstO := <|"F"-><|1->{{0.,0.},{10.,0.},{10.,10.},{0.,10.}}|>,"A"-><|1->{0,0,0,0}|>,"S"->{}
,"step"-> 0,"mList"-> <||>,"PiMList"-> <||>,"ThList"-> <||> |>;


Ori[G_,m_,Ic_,th_]:=Module[{ss,tt,mst,m2},mst=m[{ss,tt}];
m2[{xx_,yy_}]:=mst/.{ss->xx,tt->yy};
OriOld[G,m2,Ic,th]];
(*\[UpArrow]\:5165\:529b\:306e\:6298\:308a\:7ddam\:304cOri3\:306a\:3069\:3067\:8a08\:7b97\:3059\:308b\:5834\:5408,\:4e00\:5ea6\:5909\:6570\:3092\:5165\:308c\:3066\:8a08\:7b97\:3092\:7d42\:3048\:3066\:7c21\:7565\:5316\:3057\:3066\:304a\:304d\:305f\:3044!\[UpArrow]*)

Ori[G_,m_,Ic_,\[Theta]_,LR_]:=Module[{m1}, If[LR=="L",
m1[{x_,y_}]:=-(m[{x,y}]);Ori[G,-(m[{#[[1]],#[[2]]}])&,Ic,\[Theta]] 
, Ori[G,m,Ic,\[Theta]] ]];
(* \[UpArrow]L\:5074\:306e\:6298\:308a\:8ffd\:52a0*)

OriOld[G_,m_,Ic_,\[Theta]_]:=Module[{M,x,y,O2,G0=G,m0,PiM,F,C,N,mL0,pL0,tL0},
m0=m;

(*\[DownArrow]\:6298\:308a\:7dda\:9078\:629e*)

If[Length[Flatten[{m0[{x,y}]}]]!=1,
Print["-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-Fold Line Select!-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-\[DownArrow]-"];
Print[GOutput2D[G,{"Tab"-> False,"Label"-> False,"m"->m0 }]];
Print["-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-Fold Line Select!-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-\[UpArrow]-"];
Return[G] 
];
(*\[UpArrow]\:6298\:308a\:7dda\:9078\:629e*)



C=DivideFace[G0,Ic,m0];(*Ic\[RightArrow]C*)

G0=ConsGraphByDivision[G0,C,m0];(*\:5206\:5272\:64cd\:4f5c*)

If[\[Theta]==0,Return[G0]];(*\:56de\:8ee2\:306a\:3057 \:3053\:3053\:307e\:3067*)



(*\:53f3\:5074R \:56de\:8ee2\:56fa\:5b9a*)
PiM=RoteFace[G0,G0["R"],m0,\[Theta]];(*C\[RightArrow]Pi_M*)
If[!Oriable[G0,PiM,m0],Print["Cannot Ori"];Return[G]];
(*\:6298\:308a\:53ef\:80fd\:6027\:306e\:5224\:5b9a \:5206\:5272\:524d\:306e\:306eG\:3092\:8fd4\:3059*)
(* \:56de\:8ee2\:3053\:3053\:304b\:3089\[DownArrow] *)
N= G0["step"]+1; G0=Append[G0,"step"->N];(*\:30b9\:30c6\:30c3\:30d7\:6570\:8ffd\:52a0*)
mL0=Append[G0["mList"],N->m0];pL0=Append[G0["PiMList"],N->PiM];tL0=Append[G0["ThList"],N->\[Theta]];
G0=Append[G0,{"mList"-> mL0,"PiMList"->pL0,"ThList"->tL0}];(*\:5c65\:6b74*)

G0=FaceM[G0,PiM,m0];(*\:5ea7\:6a19\:5909\:63db*)
G0=KeyDrop[G0,"L"];G0=KeyDrop[G0,"R"];(*\:4e0d\:8981\:306a\:30ad\:30fc\:306e\:524a\:9664*)
G0=ConsGraphByRotation[G0,PiM,\[Theta]];(*\:56de\:8ee2\:306b\:3088\:308b\:91cd\:306a\:308a\:306e\:751f\:6210*)
Return[G0]
];




Ori::usage="Ori[G_,m_,Ic_,\[Theta]_,LR_] \:6298\:308a\:7d19G\:3092,\:6298\:308a\:7ddam\:3067,\:9762\:306eID\:96c6\:5408Ic\:3092\:542b\:3080\:9762\:3092,
\[Theta]>0\:306a\:3089\:8c37\:6298\:308a(\:4e0a\:304b\:3089\:56de\:8ee2),\[Theta]<0\:306a\:3089\:5c71\:6298\:308a(\:4e0b\:304b\:3089\:56de\:8ee2)\:3059\:308b.
LR==\[OpenCurlyDoubleQuote]L\[CloseCurlyDoubleQuote]\:306e\:3068\:304d,\:6298\:308a\:7dda\:306e\:5de6\:5074\:56de\:8ee2(\:30c7\:30d5\:30a9\:30eb\:30c8\:306f\:53f3\:5074R). ";


(* ::Text:: *)
(*OriBack*)


PiMDivid[G_]:=Module[{Fkeys,M,i,Ans={},Ans2,id=0,PL0,PiM0={},N=0,count=1},
Fkeys=Keys[G["F"]];
M=Max[Fkeys];
PL0=G["PiMList"];
N= G["step"];
PiM0=PL0[N];
Ans=Union[Ans,PiM0];

While[True,
id=Ans[[count]];
If[2id<M,Ans=Union[Ans,{2 id,2 id + 1}] ;Sort[Ans];count++, Break[]]
];(*While_end*)
Intersection[Ans,Fkeys]
];


OriBack[G_]:=OriBack[G,1];
OriBack[G_,n_]:=Module[{n0=n,i,G0=G,N,mL0,pL0,tL0,m0,PiM0,Th0},
G0=G;n0=n;
N= G0["step"];
mL0=G0["mList"];pL0=G0["PiMList"];tL0=G0["ThList"];

If[n0>N,Print["\:6570\:304c\:5927\:304d\:904e\:304e\:307e\:3059."];n0=N];



For[i=1,i<=n0,i++,
m0=mL0[N];mL0=KeyDrop[mL0,N];(*\:6298\:308a\:7dda*)
PiM0=PiMDivid[G0];pL0=KeyDrop[pL0,N];(*\:56de\:8ee2\:9762*)
Th0=tL0[N];tL0=KeyDrop[tL0,N];(*\:5c71\:6298\:308a\:8c37\:6298\:308a*)
N--;
G0=Append[G0,{"mList"-> mL0,"PiMList"->pL0,"ThList"->tL0,"step"-> N}];(*\:66f4\:65b0*)
(* \:56de\:8ee2\:3053\:3053\:304b\:3089\[DownArrow] *)
G0=FaceM[G0,PiM0,m0];(*\:5ea7\:6a19\:5909\:63db*)
G0=ConsGraphByRotation[G0,PiM0,Th0](*\:56de\:8ee2\:306b\:3088\:308b\:91cd\:306a\:308a\:306e\:751f\:6210*)
];(*For_end*)

G0
];


OriBack::usage="OriBack[G_,n_] \:6298\:308a\:7d19G\:3092n\:30b9\:30c6\:30c3\:30d7\:623b\:3059(\:958b\:304f).";


Tubushi[G_,T_,B_,Tline_,Bline_,th_]:=TubushiVer2[G,T,B,Tline,Bline,th];
TubushiVer2[G_,T_,B_,Tline_,Bline_,th_]:=
Module[{tt,LineAssoc,GG,AnoGG,TT,BB,TTline,BBline,tth,newT,newB,ii,repreT,repreB,repreedges,repreP,repreQ},
TT=T;BB=B;TTline=Tline;BBline=Bline;tth=th;
If[th<0,TT=B;BB=T;TTline=Bline;BBline=Tline;tth=th;];

GG=KeySelect[G,#=="S"||#=="F"||#=="A"&];
AnoGG=KeySelect[G,#!="S"&&#!="F"&&#!="A"&];
(*\[UpArrow]----\:6298\:308a\:306b\:5fc5\:8981\:306a\:60c5\:5831\:306e\:629c\:304d\:51fa\:3057---------*)
LineAssoc=Association[Join[Table[TT[[tt]]->TTline,{tt,1,Length[TT]}],Table[BB[[tt]]->BBline,{tt,1,Length[BB]}]]];
GG=ConsGraphByDivisionEachOne[GG,LineAssoc];
(*\[UpArrow]-----\:305d\:308c\:305d\:308c\:306e\:9762\:3092\:305d\:308c\:305e\:308c\:306e\:6298\:308a\:7dda\:3067\:5206\:5272---------*)
newT=Intersection[GG["R"],Join[TT,Map[2#+1&,TT]]];
newB=Intersection[GG["R"],Join[BB,Map[2#+1&,BB]]];
(*\[UpArrow]----\:6298\:308a\:7dda\:306e\:5411\:304d\:304c\:540c\:3058\:65b9\:5411(\:6298\:3089\:308c\:308b\:9762\:304c\:53f3\:5074(m[{x,y}]>0))\:3067\:3042\:308b\:3053\:3068\:3092\:8981\:6c42---------*)
GG=CutA[GG,newT,newB];
(*\[UpArrow]----\:96a3\:63a5\:95a2\:4fc2\:3092\:524a\:9664---------*)
GG=KeySelect[Ori[GG,TTline,newT,tth],#=="S"||#=="F"||#=="A"&];
(*\[UpArrow]----\:4e0a\:306e\:9762\:3092\:6298\:308b---------*)
GG=KeySelect[Ori[GG,BBline,newB,tth],#=="S"||#=="F"||#=="A"&];
(*\[UpArrow]----\:4e0b\:306e\:9762\:3092\:6298\:308b---------*)
ii=1;
While[ii<Length[newT]&&CutFaceQ[GG,newT[[ii]]]==0,ii=ii+1;];
repreT=newT[[ii]];
If[CutFaceQ[GG,repreT]==0,Print["\:5206\:5272\:3055\:308c\:3066\:3044\:307e\:305b\:3093."];Return[GG]];
repreB=CutFaceQ[GG,repreT];
(*\[UpArrow]----\:5207\:65ad\:3055\:308c\:305f\:8fba\:3092\:5171\:6709\:3059\:308b\:9762\:306e\:7d44(repreT,repreB)---------*)
repreedges=AdjaEdges[GG,repreT,repreB];
(*\[UpArrow]----\:5207\:65ad\:3055\:308c\:305f\:8fba\:306erepreT\:306b\:304a\:3051\:308b\:5ea7\:6a19\:3068repreB\:306b\:304a\:3051\:308b\:5ea7\:6a19---------*)
repreP=repreedges[repreT][[1]];
repreQ=repreedges[repreB][[2]];
If[Chop[Norm[repreP-repreQ]]==0,repreP=repreedges[repreT][[2]];repreQ=repreedges[repreB][[1]];];
(*\[UpArrow]----\:5bfe\:5fdc\:3059\:308b\:9802\:70b9(repreP, repreQ)---------*)
If[Chop[Norm[repreP-repreQ]]>0,GG=KeySelect[Ori[GG,LineDirectionChange[repreP,Ori2[repreP,repreQ]],newT,tth],#=="S"||#=="F"||#=="A"&]];
(*\[UpArrow]----\:5207\:65ad\:3055\:308c\:305f\:8fba\:306e\:5ea7\:6a19\:3092\:5408\:308f\:305b\:308b. ---------*)
GG=Append[GG,<|"A"->Abs[GG["A"]]|>];
(*\[UpArrow]----\:96a3\:63a5\:95a2\:4fc2\:306e\:5fa9\:5143---------*)
GG=Append[GG,AnoGG];
(*\[UpArrow]----\:305d\:306e\:4ed6\:60c5\:5831\:306e\:5fa9\:5143(\:5c65\:6b74\:306f\:4eca\:306a\:3044)---------*)
If[JudgeGoodDivide[GG["F"],GG["A"]],Return[GG]];
(*\[UpArrow]----\:304d\:3061\:3093\:3068\:623b\:3063\:3066\:3044\:308b\:304b\:5224\:5b9a---------*)
Print["\:96a3\:63a5\:95a2\:4fc2\:3068\:5ea7\:6a19\:304c\:5408\:3044\:307e\:305b\:3093. "];
Return[G];
];


Tubushi::usage="Tubushi[G_,T_,B_,Tline_,Bline_,th_] \:6298\:308a\:7d19G\:306e\:9762\:306e\:30ad\:30fc\:96c6\:5408T(\:4e0a\:90e8\:306e\:9762), B(\:4e0b\:90e8\:306e\:9762) \:3092\:305d\:308c\:305e\:308c\:6298\:308a\:7ddaTline, Bline \:3067\:6f70\:3057\:6298\:308a\:3059\:308b
(\:6f70\:3059\:9762\:304c, th>0\:3060\:3068\:4e0a, th<0\:3060\:3068\:4e0b, \:306b\:6765\:308b). ";


Kabuse[G_,m_,T_,B_]:=KabuseVer1[G,m,T,B];
KabuseVer1[G_,m_,T_,B_]:=Module[{GG,AnoGG,newT,newB,GGset,GGset1,GGset2},
If[Length[Intersection[T,B]]>0,
Print["\[Phi] \[NotEqual] T \[Intersection] B \:3067\:3059. "];Return[G]];
If[Length[Complement[Keys[G["F"]],Join[T,B]]]>0||Length[Complement[Join[T,B],Keys[G["F"]]]]>0,
Print["\[CapitalPi] \[NotEqual] T \[Union] B\:3067\:3059. "];Return[G]];
(*\[UpArrow]----\:5165\:529b\:304c\:6b63\:3057\:3044\:304b?---------*)
GG=KeySelect[G,#=="S"||#=="F"||#=="A"&];
AnoGG=KeySelect[G,#!="S"&&#!="F"&&#!="A"&];
(*\[UpArrow]----\:6298\:308a\:306b\:5fc5\:8981\:306a\:60c5\:5831\:306e\:629c\:304d\:51fa\:3057---------*)
GG=ConsGraphByDivision[GG,Join[T,B],m];
(*\[UpArrow]----\:9762\:306e\:5206\:5272---------*)
newT=Intersection[Keys[GG["F"]],Join[T,Map[2#+1&,T],Map[2#&,T]]];
newB=Intersection[Keys[GG["F"]],Join[B,Map[2#+1&,B],Map[2#&,B]]];
(*\[UpArrow]----\:5206\:5272\:5f8c\:306eT,B---------*)
GGset=CutOrigami[GG,{newT,newB}];
(*\[UpArrow]----GG\:3092\:5206\:5272 \:91cd\:306a\:308a\:95a2\:4fc2\:3082\:5207\:308b\:72ec\:7acb\:3057\:305f\:6298\:308a\:7d19\:306b\:3059\:308b. ---------*)
GGset1=KeySelect[Ori[GGset[[1]],m,newT,1],#=="S"||#=="F"||#=="A"&];
GGset2=KeySelect[Ori[GGset[[2]],m,newB,-1],#=="S"||#=="F"||#=="A"&];
(*\[UpArrow]----\:4e0a\:306e\:9762, \:4e0b\:306e\:9762\:3092\:6298\:308b. \:4e2d\:5272\:308a\:6298\:308a\:3068\:306e\:9055\:3044\:306f\:3053\:3053\:3060\:3051(in 2015/12/01)---------*)
GG=AddOrigami[GGset2,GGset1];
(*\[UpArrow]----2\:3064\:306e\:6298\:308a\:7d19\:3092\:7e4b\:3052\:76f4\:3059---------*)
GG=Append[GG,"A"->Abs[GG["A"]]];
GG=Append[GG,AnoGG];
(*\[UpArrow]----\:96a3\:63a5\:95a2\:4fc2\:3092\:623b\:3059---------*)
If[JudgeGoodDivide[GG["F"],GG["A"]],Return[GG]];
(*\[UpArrow]----\:304d\:3061\:3093\:3068\:623b\:3063\:3066\:3044\:308b\:304b\:5224\:5b9a---------*)
Print["\:96a3\:63a5\:95a2\:4fc2\:3068\:5ea7\:6a19\:304c\:5408\:3044\:307e\:305b\:3093. "];
Return[G];
]


Kabuse::usage="Kabuse[G_,m_,T_,B_] \:6298\:308a\:7d19G\:306e\:9762\:306e\:30ad\:30fc\:96c6\:5408T(\:4e0a\:90e8\:306e\:9762), B(\:4e0b\:90e8\:306e\:9762) \:3092\:6298\:308a\:7ddam \:3067\:304b\:3076\:305b\:6298\:308a\:3092\:3059\:308b. ";


Nakawari[G_,m_,T_,B_,TIc_,BIc_]:=NakawariVer3[G,m,T,B,TIc,BIc];
NakawariVer3[G_,m_,T_,B_,TIc_,BIc_]:=Module[{GG,AnoGG,newT,newB,newTIc,newBIc,GGset,GGset1,GGset2},
newT=Intersection[TransitiveR[G,T,"Overlap",1],TransitiveR[G,T,"S",1]];
newB=Intersection[TransitiveR[G,B,"Overlap",1],TransitiveR[G,B,"S",-1]];
If[Length[Intersection[newT,newB]]>0,
Print["\[Phi] \[NotEqual] T \[Intersection] B \:3067\:3059. "];Return[G]];
If[Length[Complement[Keys[G["F"]],Join[newT,newB]]]>0||Length[Complement[Join[newT,newB],Keys[G["F"]]]]>0,
Print["\[CapitalPi] \[NotEqual] T \[Union] B\:3067\:3059. "];Return[G]];
(*\[UpArrow]----\:5165\:529b\:304c\:6b63\:3057\:3044\:304b?---------*)
GG=KeySelect[G,#=="S"||#=="F"||#=="A"&];
AnoGG=KeySelect[G,#!="S"&&#!="F"&&#!="A"&];
(*\[UpArrow]----\:6298\:308a\:306b\:5fc5\:8981\:306a\:60c5\:5831\:306e\:629c\:304d\:51fa\:3057---------*)
GG=ConsGraphByDivision[GG,DivideFace[GG,Join[TIc,BIc],m],m];
(*\[UpArrow]----\:9762\:306e\:5206\:5272---------*)
newT=Intersection[Keys[GG["F"]],Join[newT,Map[2#+1&,newT],Map[2#&,newT]]];
newB=Intersection[Keys[GG["F"]],Join[newB,Map[2#+1&,newB],Map[2#&,newB]]];
newTIc=Intersection[Keys[GG["F"]],Join[TIc,Map[2#+1&,TIc]]];
newBIc=Intersection[Keys[GG["F"]],Join[BIc,Map[2#+1&,BIc]]];
(*\[UpArrow]----\:5206\:5272\:5f8c\:306eT,B,TIc,BIc---------*)
GGset=CutOrigami[GG,{newT,newB}];
(*\[UpArrow]----GG\:3092\:5206\:5272 \:91cd\:306a\:308a\:95a2\:4fc2\:3082\:5207\:308b\:72ec\:7acb\:3057\:305f\:6298\:308a\:7d19\:306b\:3059\:308b. ---------*)
GGset1=KeySelect[Ori[GGset[[1]],m,newTIc,-1],#=="S"||#=="F"||#=="A"&];
GGset2=KeySelect[Ori[GGset[[2]],m,newBIc,1],#=="S"||#=="F"||#=="A"&];
(*\[UpArrow]----\:4e0a\:306e\:9762, \:4e0b\:306e\:9762\:3092\:6298\:308b. \:3053\:3053\:3067\:9762\:756a\:53f7\:304c\:5909\:308f\:308b\:3068\:623b\:305b\:306a\:3044\:306e\:3067\:6ce8\:610f---------*)
GG=AddOrigami[GGset2,GGset1];
(*\[UpArrow]----2\:3064\:306e\:6298\:308a\:7d19\:3092\:7e4b\:3052\:76f4\:3059---------*)
GG=Append[GG,"A"->Abs[GG["A"]]];
(*\[UpArrow]----\:96a3\:63a5\:95a2\:4fc2\:3092\:623b\:3059---------*)
GG=Append[GG,AnoGG];
If[JudgeGoodDivide[GG["F"],GG["A"]],Return[GG]];
(*\[UpArrow]----\:304d\:3061\:3093\:3068\:623b\:3063\:3066\:3044\:308b\:304b\:5224\:5b9a---------*)
Print["\:96a3\:63a5\:95a2\:4fc2\:3068\:5ea7\:6a19\:304c\:5408\:3044\:307e\:305b\:3093. "];
Print["G=",GG];
Return[G];
];


Nakawari::usage="Nakawari[G_,m_,T_,B_,TIc_,BIc_] \:6298\:308a\:7d19G\:306e\:9762\:306e\:30ad\:30fc\:96c6\:5408T(\:4e0a\:90e8\:306e\:9762), B(\:4e0b\:90e8\:306e\:9762)\:306e\:305d\:308c\:305e\:308c\:306e
\:90e8\:5206\:96c6\:5408TIc, BIc(\:6298\:308b\:9762) \:3092\:6298\:308a\:7ddam \:3067\:4e2d\:5272\:308a\:6298\:308a\:3092\:3059\:308b. ";



(*----------\[DownArrow]\:53e4\:5178\:6298\:308a\:306e\:5185\:90e8\:95a2\:6570---------------*)
FaceDivideEachOne[G_,FMset_]:=Module[{Ic0,A1,F0,A0,Al04,i,L,R,Ai,j,Absi,LL,RR,m},
Ic0=Keys[FMset];
F0=G["F"];A0=G["A"];A1=A0;
L=<||>;R=<||>;
While[Ic0!= {},
i=First[Ic0];
m=FMset[i];
Al04=Algorithm04Re[F0,A0,i,m];
F0=Al04[[1]];A0=Al04[[2]];
If[Al04[[3]],
AssociateTo[L,i-> 2i];AssociateTo[R,i-> (2i+1)]
,(*0 or 1*)
(*\[DownArrow]F0&A0\:66f4\:65b0*)
If[Length[F0[2i]]<= 2,AssociateTo[R,i->i];
AppendTo[F0,i->F0[(2i+1)]] ;KeyDropFrom[F0,{2i,(2i+1)}] ;
AppendTo[A0,i->A1[i]] ;KeyDropFrom[A0,{2i,(2i+1)}]  ];
If[KeyExistsQ[F0,2i+1] && Length[F0[(2i+1)]]<= 2,AssociateTo[L,i->i];
AppendTo[F0,i->F0[2i]];KeyDropFrom[F0 ,{2i,(2i+1)}];
AppendTo[A0,i->A1[i]];KeyDropFrom[A0 ,{2i,(2i+1)}]   ]
];(*If_end*)

Ic0=Rest[Ic0];
];(*While_end*)
(*\:3053\:3053\:3089\:3067\:5224\:5b9a*)

(*\:66f8\:304d\:63db\:3048\[DownArrow]*)
(*\:5de6\:306e\:3068\:304d*)
Ic0=Join[Values[L],
Complement[Union[Flatten[Map[A0[#]&,Values[L]]]](*\[LeftArrow]\:96a3\:63a5\:3057\:3066\:3044\:308b\:5de6\:306e\:8981\:7d20*),{0},Keys[L],Values[R]]];
While[Ic0!= {},
i=First[Ic0];
Absi=Abs[i];
Ai=A0[Absi];
If[Sign[i]>0,LL=L,LL=Association[Flatten[Map[#->-L[#]&,Keys[L]]]]];
AssociateTo[A0,Absi->(Ai/.LL)];
Ic0=Rest[Ic0];
];(*While_end*)
(*\:53f3\:306e\:3068\:304d*)
Ic0=Join[Values[R],
Complement[Union[Flatten[Map[A0[#]&,Values[R]]]](*\[LeftArrow]\:96a3\:63a5\:3057\:3066\:3044\:308b\:53f3\:306e\:8981\:7d20*),{0},Keys[R],Values[L]]];
While[Ic0!= {},
i=First[Ic0];
Absi=Abs[i];
Ai=A0[Absi];
If[Sign[i]>0,RR=R,RR=Association[Flatten[Map[#->-R[#]&,Keys[R]]]]];
AssociateTo[A0,Absi->(Ai/.RR)];
Ic0=Rest[Ic0];
];(*While_end*)
If[JudgeGoodDivide[F0,A0],Return[{F0,A0,Values[L],Values[R]}],Return[G]];
];
FaceDivideEachOne::usage="FaceDivideEachOne[G_,FMset_] \:305d\:308c\:305e\:308c\:306e\:9762\:306b\:5bfe\:3057\:3066
\:6c7a\:3081\:3089\:308c\:305f\:6298\:308a\:7dda(\:9023\:60f3\:914d\:5217)\:3067\:5206\:5272\:3059\:308b.(\:91cd\:306a\:308a\:95a2\:4fc2\:306f\:7121\:8996)";

ConsGraphByDivisionEachOne[G_,FMset_]:=
Module[{GK,FALR,F=G["F"],A=G["A"],L,R,OldFKey,S=G["S"],G1,S1},
OldFKey=Keys[F];
FALR=FaceDivideEachOne[G,FMset];
F=FALR[[1]];
A=FALR[[2]];
L=FALR[[3]];
R=FALR[[4]];
G1=Append[G,<|"F"->F,"A"->A,"L"->L,"R"->R|>];
GK=GraphDivision[Append[G1,<|"S"->{}|>],{},OldFKey,S];
G1=GK[[1]];
S1=G1["S"];
S1=SSimple[S1];
Return[Append[G1,<|"S"->S1|>]]
];
ConsGraphByDivisionEachOne::usage="ConsGraphByDivisionEachOne[G_,FMset_] 
\:305d\:308c\:305e\:308c\:306e\:9762\:306b\:5bfe\:3057\:3066\:6c7a\:3081\:3089\:308c\:305f\:6298\:308a\:7dda(\:9023\:60f3\:914d\:5217)\:3067\:91cd\:306a\:308a\:95a2\:4fc2\:3092\:4fdd\:3061\:306a\:304c\:3089\:5206\:5272\:3059\:308b.";

AdjaEdges[G_,fkey1_,fkey2_]:=Module[{f1A,f2A,f1Po,f2Po,f1Ed,f2Ed},
f1A=Abs[G["A"][fkey1]];
f2A=Abs[G["A"][fkey2]];
If[!(MemberQ[f1A,fkey2] && MemberQ[f2A,fkey1]),Return[<||>]];
f1Po=FirstPosition[f1A,fkey2];
f2Po=FirstPosition[f2A,fkey1];
f1Ed={Mod[f1Po-1,Length[f1A],1],f1Po};
f2Ed={Mod[f2Po-1,Length[f2A],1],f2Po};
<|fkey1->Map[Flatten[G["F"][fkey1][[#]]]&,f1Ed],fkey2->Map[Flatten[G["F"][fkey2][[#]]]&,f2Ed]|>
];
AdjaEdges::usage="AdjaEdges[G_,fkey1_,fkey2_] \:6298\:308a\:7d19G \:306b\:304a\:3044\:3066\:9762fkey1,fkey2\:306e\:5171\:6709\:3059\:308b\:8fba\:306e\:5ea7\:6a19\:3092\:8fd4\:3059.";

EdgesEqality[{Edge1_,Edge2_}]:=Chop[Norm[Edge1-Edge2]]==0||Chop[Norm[Edge1-{Edge2[[2]],Edge2[[1]]}]]==0;
EdgesEqality::usage="EdgesEqality[{E1_,E2_}] \:ff12\:7dda\:5206E1,E2\:304c\:7b49\:3057\:3044\:304b\:3092\:8abf\:3079\:308b.";

JudgeGoodDivideOnOne[F0_,A0_,Fkey_]:=
If[Length[Select[A0[Fkey],#!=0&]]===
Count[Map[EdgesEqality[Values[AdjaEdges[<|"F"->F0,"A"->A0|>,Abs[#],Abs[Fkey]]]]&,Select[A0[Fkey],#!=0&]],True],
Return[True],Print["\:9762",Fkey,"\:3092\:78ba\:8a8d\:3057\:3066\:304f\:3060\:3055\:3044"];Return[False]];
JudgeGoodDivideOnOne::usage="JudgeGoodDivideOnOne[F0_,A0_,Fkey_] 
\:9762\:96c6\:5408F0(\:9023\:60f3\:914d\:5217),\:96a3\:63a5\:95a2\:4fc2A0 \:306b\:304a\:3044\:3066 \:9762fkey\:306e\:96a3\:63a5\:95a2\:4fc2\:306f\:6b63\:3057\:3044\:304b.";

JudgeGoodDivide[F0_,A0_]:=Length[Keys[F0]]===Count[Map[JudgeGoodDivideOnOne[F0,A0,#]&,Keys[F0]],True];
JudgeGoodDivide::usage="JudgeGoodDivide[F0_,A0_] \:9762\:96c6\:5408F0(\:9023\:60f3\:914d\:5217)\:3068\:96a3\:63a5\:95a2\:4fc2A0 \:306e\:95a2\:4fc2\:306b\:77db\:76fe\:304c\:306a\:3044\:304b.";

LineDirectionChange[x_,m_]:=LineDirectionChangeVer2[x,m];
LineDirectionChangeVer1[x_,m_]:=If[m[x]<0,Return[-m[{#[[1]],#[[2]]}]&],Return[m]];
LineDirectionChangeVer2[x_,m_]:=Module[{tt1,tt2},If[(m[{tt1,tt2}]/.{tt1->x[[1]],tt2->x[[2]]})<0,
Return[-m[{#[[1]],#[[2]]}]&]];Return[m]];
LineDirectionChange::usage="LineDirectionChange[x_,m_] m\:306e\:65b9\:5411\:306fx\:304c\:53f3\:306b\:306a\:308b\:3088\:3046\:306b\:3059\:308b.";

CutA[G_,T_,B_]:=Module[{CutedOrigami,SubstituteT,SubstituteB,TA,BA},
SubstituteT=Flatten[Map[#->-#&,B]];
SubstituteB=Flatten[Map[#->-#&,T]];
TA=Association[Flatten[Map[#->(G["A"][#]/.SubstituteT)&,T]]];
BA=Association[Flatten[Map[#->(G["A"][#]/.SubstituteB)&,B]]];
CutedOrigami=Append[G,<|"A"->Append[Append[G["A"],TA],BA]|>];
CutedOrigami
];
CutA::usage="CutA[G_,T_,B_] \:9762\:96c6\:5408T, B\:306e\:96a3\:63a5\:95a2\:4fc2\:3092\:5207\:308b.";

CutFaceQ[G_,fkey_]:=If[Length[Select[G["A"][fkey],#<0&]]>0,-Select[G["A"][fkey],#<0&][[1]],0];
CutFaceQ::usage="CutFaceQ[G_,fkey_] \:9762fkey\:306e\:96a3\:63a5\:95a2\:4fc2\:304c\:5207\:3089\:308c\:3066\:3044\:308b\:304b\:5224\:5b9a(\:5207\:3089\:308c\:305f\:5148\:306e\:9762\:756a\:53f7\:3092\:8fd4\:3059).";

CutOrigami[G_,TBSets_]:=Module[{CutedOrigami,AllFKeys,KeySelectbySet},
AllFKeys=Keys[G["F"]];
KeySelectbySet[GG_,Sets_]:=<|"F"->KeySelect[GG["F"],MemberQ[Sets,#]&],"A"->Association[Flatten[Map[#->(G["A"][#]/.Flatten[Map[#->-#&,Complement[AllFKeys,Sets]]])&,Keys[KeySelect[GG["A"],MemberQ[Sets,#]&]]]]],"S"->Select[GG["S"],MemberQ[Sets,#[[1]]]&&MemberQ[Sets,#[[2]]]&]|>;
CutedOrigami=Map[KeySelectbySet[G,#]&,TBSets];
CutedOrigami
];
CutOrigami::usage="CutOrigami[G_,{T,B}_] \:6298\:308a\:7d19G \:3092\:305d\:306e\:9762\:306e\:30ad\:30fc\:306e\:90e8\:5206\:96c6\:5408T(\:4e0a\:90e8\:306e\:9762), B(\:4e0b\:90e8\:306e\:9762) \:306b\:5206\:5272\:3057\:305f\:6298\:308a\:7d19\:3092\:8fd4\:3059. ";

AddOrigami[G1_,G2_]:=
Module[{GK,G0,S0,PeakG0,AnsG,AnsS},
If[Length[Intersection[Keys[G1["F"]],Keys[G2["F"]]]]>=1,Print["G1\:3068G2\:306b\:5171\:901a\:3059\:308b\:9762\:756a\:53f7\:304c\:3042\:308a\:307e\:3059. in AddOrigami."]];
G0=Append[<|"F"->Append[G1["F"],G2["F"]],"A"->Append[G1["A"],G2["A"]],"S"->G1["S"]|>,Append[KeyDrop[G1,{"F","A","S"}],KeyDrop[G2,{"F","A","S"}]]];

PeakG0=Peak[Keys[G1["F"]],G1["S"]];

GK=GraphRotation[G0,PeakG0,Keys[G2["F"]],G2["S"]];
AnsG=GK[[1]];
AnsS=AnsG["S"];
AnsS=SSimple[AnsS];
AnsG=Append[AnsG,<|"S"->AnsS|>];
Return[AnsG];
];
AddOrigami::usage="AddOrigami[G1_,G2_] \:6298\:308a\:7d19G1,G2 \:3092\:304f\:3063\:3064\:3051\:308b(G2\:3092\:4e0a\:3068\:3059\:308b). ";


EndPackage[];
