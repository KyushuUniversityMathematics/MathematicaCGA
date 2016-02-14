(* ::Package:: *)

(* ::Title:: *)
(*CGA5Package.m*)


(* ::Text:: *)
(*Copyright (c) 2015  Mitsuhiro Kondo , Takuya Matsuo , Yoshihiro Mizoguchi , Hiroyuki Ochiai , Kyushu University*)
(**)
(*Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell*)
(*copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:*)
(*The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.*)
(*THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.*)


(* ::Text:: *)
(*\:6700\:7d42\:66f4\:65b0\:65e5:2015/08/06 *)
(*\:4f5c\:6210\:65e5:2014/06/19 *)


(* ::Text:: *)
(*\:540c\:540d\:306e\:30b7\:30f3\:30dc\:30eb\:306e\:7af6\:5408\:3092\:907f\:3051\:308b\:305f\:3081\:30b3\:30f3\:30c6\:30ad\:30b9\:30c8\:3092\:5b9a\:3081\:308b*)


BeginPackage["CGA5Package`"];


(* ::Text:: *)
(*\:30d1\:30c3\:30b1\:30fc\:30b8\:5185\:306e\:307f\:3067\:5229\:7528\:3059\:308b\:95a2\:6570\:3092\:30b3\:30f3\:30c6\:30ad\:30b9\:30c8 `Private` \:5185\:3067\:5b9a\:7fa9\:3059\:308b.*)


Begin["`Private`"];

End[];


(* ::Text:: *)
(*CGAProduct\:306e\:5b9a\:7fa9*)


(*CGAProduct\:306e\:5b9a\:7fa9:\:5165\:529bw[_]\:306e\:4e2d\:8eab\:306f\:30bd\:30fc\:30c8\:3057\:3066\:304a\:304f\:3068\:4eee\:5b9a:w[{}]\:306f\:30b9\:30ab\:30e9\:30fc*)
(*\:7dda\:5f62\:6027*)
(*\:7dda\:5f62\:6027:(G1)\:5206\:914d\:5247*)
CGAproduct[x_+y_,z_]:=CGAproduct[x,z]+CGAproduct[y,z];
CGAproduct[x_,y_+z_]:= CGAproduct[x, y]+CGAproduct[x, z];
(*\:7dda\:5f62\:6027:(G2)\:30b9\:30ab\:30e9\:30fc\:500d*)
CGAproduct[a_ w[x_],y_]:=Expand[a CGAproduct[wTFe[w[x]],y]];
CGAproduct[x_,a_ w[y_]]:=Expand[a CGAproduct[x, wTFe[w[y]]]];
CGAproduct[a_ e[x_],y_]:=Expand[a CGAproduct[e[x],y]];
CGAproduct[x_,a_ e[y_]]:=Expand[a CGAproduct[x, e[y]]];
(*\:5f0f\:306e\:6574\:7406*)
CGAproduct[x_ y_,z_]:= CGAproduct[Expand[x y], z];
CGAproduct[x_ ,y_ z_]:= CGAproduct[x , Expand[y z]];

(*0\:500d*)
CGAproduct[x_,0]:=0;
CGAproduct[0,y_]:=0;
CGAproduct[x_,0.]:=0;
CGAproduct[0.,y_]:=0;
(*\:57fa\:5e95\:3092\:53d6\:308a\:66ff\:3048\:308b*)
CGAproduct[w[x_],w[y_]]:=CGAproduct[wTFe[w[x]],wTFe[w[y]]];
CGAproduct[w[x_],e[y_]]:=CGAproduct[wTFe[w[x]],e[y]];
CGAproduct[e[x_],w[y_]]:=CGAproduct[e[x],wTFe[w[y]]];

CGAproduct[ e[{}],e[S_]]:=e[S];


(*\:ff11\:3064\:76ee\:306e\:8981\:7d20\:304c w[{0}]\:306e\:3068\:304d(\:305f\:3060\:30570*\[Infinity] \[Equal] -1 +0^\[Infinity])*)
CGAproduct[ e[{0}],e[S_]]:=
 If[Count[S,0]==0,(*0\:542b\:307e\:305a*)e[Join[{0},S]],(*0\:542b\:3080*)0];
(*\:ff11\:3064\:76ee\:306e\:8981\:7d20\:304c w[{\[Infinity]}]\:306e\:3068\:304d (\:305f\:3060\:3057\[Infinity]*0 \[Equal] -1 -0^\[Infinity])*)
CGAproduct[ e[{\[Infinity]}],e[S_]]:=
 If[Count[S,0]==0,
 (*0\:542b\:307e\:305a*)If[Count[S,\[Infinity]]==0,(*\[Infinity]\:542b\:307e\:305a*)(-1)^Length[S]*e[Join[S,{\[Infinity]}]],(*\[Infinity]\:542b\:3080*)0],
 (*0\:542b\:3080*)-CGAproduct[e[{0}],
			CGAproduct[e[{\[Infinity]}],e[Complement[S,{0}]]]]-2e[Complement[S,{0}]]];

(*\:ff11\:3064\:76ee\:306e\:8981\:7d20\:6570=1 \:306e\:3068\:304d\:3001\:771f:\:540c\:3058\:3082\:306e\:304c\:542b\:307e\:308c\:3066\:3044\:306a\:3044\[RightArrow]\:30bd\:30fc\:30c8\:3057\:3066\:7b26\:53f7\:3092\:5909\:3048\:308b(\[Because] \:53cd\:4ea4\:63db\:6027)\:3001
\:507d:\:540c\:3058\:3082\:306e\:304c\:542b\:307e\:308c\:3066\:3044\:308b\[RightArrow]\:540c\:3058\:8981\:7d20\:306e\:6d88\:53bb(\[Because] X*X\[Equal]1,X\[Element]{1,2,3})*)
CGAproduct[ e[{a_}],e[S_]]:=
 If[Count[S,a]==0,
  (*a\:542b\:307e\:305a*)Signature[Join[{a},S]]*e[Sort[Join[{a},S]]],
  (*a\:542b\:3080*)Signature[Join[{a},Complement[S,{a}]]]*e[Complement[S,{a}]] ];

(*\:ff11\:3064\:76ee\:306e\:8981\:7d20\:3092\:5f8c\:308d\:304b\:3089\:9806\:756a\:306b\:304b\:3051\:308b:\:518d\:5e30\:6027,\:5358\:4f4d\:5143\:306e\:7a4d\:3082\:542b\:3080*)
(*CGAproduct[e[T_],e[S_]]:=Module[{i,aS=e[S]},For[i=Length[T],i>0,i=i-1,
 aS=CGAproduct[e[{T[[i]]}],aS]];aS];*)

CGAproduct[e[T_],e[S_]]:=CGAproduct[e[Drop[T,-1]],
CGAproduct[e[Take[T,-1]],e[S]] ];


(*Collect:e\:306e\:5404\:30d9\:30ad\:3092\:307e\:3068\:3081\:308b , Simplify:\:5404\:4fc2\:6570\:3092\:7c21\:7d04 ,
 eTFw:e\[Rule]w\:3078, Expand:\:5c55\:958b , Chop:\:5207\:308a\:6368\:3066*)
CGAProduct[x_,y_]:=Collect[eTFw[Expand[Chop[CGAproduct[x,y]]]],w[_],Simplify];


(* Complement\:4f7f\:308f\:305a\:ff1a
CGAproduct[ e[{\[Infinity]}],e[S_]]:=
If[Count[S,0]==0,
(*0\:542b\:307e\:305a*)If[Count[S,\[Infinity]]==0,(*\[Infinity]\:542b\:307e\:305a*)(-1)^Length[S]*e[Join[S,{\[Infinity]}]],(*\[Infinity]\:542b\:3080*)0],
(*0\:542b\:3080*)-CGAproduct[e[{0}],CGAproduct[e[{\[Infinity]}],e[Delete[S,1]]]]-2e[Delete[S,1]]];
(*\:ff11\:3064\:76ee\:306e\:8981\:7d20\:6570=1 \:306e\:3068\:304d\:3001\:771f:\:540c\:3058\:3082\:306e\:304c\:542b\:307e\:308c\:3066\:3044\:306a\:3044\[RightArrow]\:30bd\:30fc\:30c8\:3057\:3066\:7b26\:53f7\:3092\:5909\:3048\:308b(\[Because] \:53cd\:4ea4\:63db\:6027)\:3001
\:507d:\:540c\:3058\:3082\:306e\:304c\:542b\:307e\:308c\:3066\:3044\:308b\[RightArrow]\:540c\:3058\:8981\:7d20\:306e\:6d88\:53bb(\[Because] X*X\[Equal]1,X\[Element]{1,2,3})*)
CGAproduct[ e[{x_}],e[y_]]:=
If[Count[y,x]==0,
Signature[Join[{x},y]]*e[Sort[Join[{x},y]]],
(-1)^(Position[y,x][[1]][[1]]-1)e[Delete[y,Position[y,x][[1]][[1]]]]];

(*\:ff11\:3064\:76ee\:306e\:8981\:7d20\:3092\:5f8c\:308d\:304b\:3089\:9806\:756a\:306b\:304b\:3051\:308b:\:518d\:5e30\:6027,\:5358\:4f4d\:5143\:306e\:7a4d\:3082\:542b\:3080*)
CGAproduct[e[T_],e[S_]]:=Module[{i,aS=e[S]},For[i=Length[T],i>0,i=i-1,
 aS=CGAproduct[e[{T[[i]]}],aS]];aS];
*)


(*\:5f15\:6570\:304c\:8907\:6570\:306e\:5834\:5408\:306b\:5bfe\:5fdc*)
CGAProduct[x_,y_,z_]:=CGAProduct[CGAProduct[x,y],z];
CGAProduct[x_,y_,z_,w_]:=CGAProduct[CGAProduct[CGAProduct[x,y],z],w];
CGAProduct[X_]:=Module[{i,Y=w[{}]},
 For[i=1,i<=Length[X],i++,Y=CGAProduct[ Y,X[[i]]] ];Y];


(* ::Text:: *)
(*CGAProduct\:306e\:8aac\:660e*)


CGAProduct::usage="CGAProduct[x,y] CGA\:306e\:5143x\:3068y\:306egeometric\:7a4d\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*gr\:306e\:5b9a\:7fa9*)


(*grade\:3092\:6c42\:3081\:308b*)
gr[w[x_]] := Length[x];
(*\:7dda\:5f62\:6027*)
gr[a_ w[x_]]:=Length[x];
gr[X_+Y_]:=Max[gr[X],gr[Y]];


(* ::Text:: *)
(*gr\:306e\:8aac\:660e*)


gr::usage="gr[x] CGA\:306e\:5143x\:306egrade\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*PickUp\:306e\:5b9a\:7fa9*)


(*grade\:304ck\:306e\:90e8\:5206\:3092\:629c\:304d\:51fa\:3059*)
PickUp[w[x_],k_]:=If[Length[x]==k,w[x],0];
(*\:7dda\:5f62\:6027*)
PickUp[x_+y_,k_]:=PickUp[x,k]+PickUp[y,k];
PickUp[a_ w[x_],k_]:=a PickUp[w[x],k];
PickUp[0,k_]:=0;

PickUp[e[x_],k_]:=PickUp[eTFw[e[x]],k];
PickUp[a_ e[x_],k_]:=a PickUp[eTFw[e[x]],k];


(*grade\:304ck\:306e\:90e8\:5206\:306e\:4fc2\:6570\:30ea\:30b9\:30c8\:3092\:629c\:304d\:51fa\:3059*)
CoefPickUp[w[x_],k_]:=If[gr[w[x]]==k,{1},{0}];
CoefPickUp[a_ w[x_],k_]:=If[gr[w[x]]==k,{a},{0}];
CoefPickUp[0,k_]:={};
CoefPickUp[x_+y_,k_]:=Join[CoefPickUp[x,k],CoefPickUp[y,k]];
(*\:3059\:3079\:3066\:306e\:57fa\:5e95\:306e\:4fc2\:6570\:30ea\:30b9\:30c8\:3092\:629c\:304d\:51fa\:3059*)
CoefPickUp[w[x_]]:={1};
CoefPickUp[a_ w[x_]]:={a};
CoefPickUp[0]:={};
CoefPickUp[x_+y_]:=Join[CoefPickUp[x],CoefPickUp[y]];
CoefPickUp[x_]:={};


CoefPickUp1[a_ w[x_],k_]:=If[gr[w[x]]==k,a,0];


(* ::Text:: *)
(*PickUp\:306e\:8aac\:660e*)


PickUp::usage="PickUp[x,k] CGA\:306e\:5143x\:306egrade k\:306e\:90e8\:5206\:3092\:6c42\:3081\:308b.";
CoefPickUp::usage="CoefPickUp[x,k] CGA\:306e\:5143x\:306egrade k\:306e\:90e8\:5206\:306e\:4fc2\:6570\:30ea\:30b9\:30c8\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*OuterProduct\:306e\:5b9a\:7fa9*)


(*\:7dda\:5f62\:6027*)
OuterProduct[x_+y_,z_]:=Collect[OuterProduct[x,z]+OuterProduct[y,z],w[_],Simplify];
OuterProduct[x_,y_+z_]:= Collect[OuterProduct[x, y]+OuterProduct[x, z],w[_],Simplify];
OuterProduct[a_ w[x_],y_]:=Expand[a OuterProduct[w[x],y]];
OuterProduct[x_,a_ w[y_]]:=Expand[a OuterProduct[x, w[y]]];
(*0\:500d*)
OuterProduct[x_,0]:=0;
OuterProduct[0,y_]:=0;
OuterProduct[x_,0.]:=0;
OuterProduct[0.,y_]:=0;
(*Blade\:540c\:58eb\:306e\:7a4d\:306e\:6700\:5927\:306eGrade\:304c\:5916\:7a4d\:3068\:306a\:3063\:3066\:3044\:308b*)
OuterProduct[w[x_],w[y_]]:=PickUp[CGAProduct[w[x],w[y]],gr[w[x]]+gr[w[y]]];

OuterProduct[x_]:=Module[{i,Y=w[{}]},For[i=1,i<=Length[x],i++,Y=OuterProduct[x[[i]],Y]];Y]


(*\:5f15\:6570\:304c\:8907\:6570\:306e\:5834\:5408\:306b\:5bfe\:5fdc*)
OuterProduct[x_,y_,z_]:=OuterProduct[OuterProduct[x,y],z];
OuterProduct[x_,y_,z_,w_]:=OuterProduct[OuterProduct[OuterProduct[x,y],z],w];
OuterProduct[X_]:=Module[{i,Y=w[{}]},For[i=1,i<=Length[X],i++,Y=OuterProduct[ Y,X[[i]]] ];Y];


(* ::Text:: *)
(*OuterProduct\:306e\:8aac\:660e*)


OuterProduct::usage="OuterProduct[x,y] CGA\:306e\:5143x\:3068y\:306e\:5916\:7a4d\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*InnerProduct\:306e\:5b9a\:7fa9*)


(*\:7dda\:5f62\:6027*)
InnerProduct[x_+y_,z_]:=Collect[InnerProduct[x,z]+InnerProduct[y,z],w[_],Simplify];
InnerProduct[x_,y_+z_]:= Collect[InnerProduct[x, y]+InnerProduct[x, z],w[_],Simplify];
InnerProduct[a_ w[x_],y_]:=Expand[a InnerProduct[w[x],y]];
InnerProduct[x_,a_ w[y_]]:=Expand[a InnerProduct[x, w[y]]];
(*0\:500d*)
InnerProduct[x_,0]:=0;
InnerProduct[0,y_]:=0;
InnerProduct[x_,0.]:=0;
InnerProduct[0.,y_]:=0;
(*Blade\:540c\:58eb\:306e\:7a4d\:306e\:6700\:5c0f\:306eGrade\:304c\:5185\:7a4d\:3068\:306a\:3063\:3066\:3044\:308b*)
InnerProduct[w[x_],w[y_]]:=PickUp[CGAProduct[w[x],w[y]],Abs[gr[w[x]]-gr[w[y]]]];


(*\:5f15\:6570\:304c\:8907\:6570\:306e\:5834\:5408\:306b\:5bfe\:5fdc*)
InnerProduct[x_,y_,z_]:=InnerProduct[InnerProduct[x,y],z];
InnerProduct[x_,y_,z_,w_]:=InnerProduct[InnerProduct[InnerProduct[x,y],z],w];
InnerProduct[X_]:=Module[{i,Y=w[{}]},For[i=1,i<=Length[X],i++,Y=InnerProduct[ Y,X[[i]]] ];Y];


(* ::Text:: *)
(*InnerProduct\:306e\:8aac\:660e*)


InnerProduct::usage="InnerProduct[x,y] CGA\:306e\:5143x\:3068y\:306e\:5185\:7a4d\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*Dual\:306e\:5b9a\:7fa9*)


Dual[x_]:=CGAProduct[x,-w[{0,1,2,3,\[Infinity]}]];


(* ::Text:: *)
(*Dual\:306e\:8aac\:660e*)


Dual::usage="Dual[x] CGA\:306e\:5143x\:306e\:53cc\:5bfe(Dual)\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*eTFw , wTFe\:306e\:5b9a\:7fa9*)


(*e\[Rule]w*)
eTFw[x_+y_]:=eTFw[x]+eTFw[y];
eTFw[a_ e[x_]]:=Expand[a eTFw[e[x]]];
eTFw[a_ w[x_]]:=Expand[a w[x]];

eTFw[e[S_]]:=If[Count[S,0]>0 && Count[S,\[Infinity]]>0,
 w[S]-(-1)^Length[S] *w[Complement[S,{0,\[Infinity]}]], w[S]];

eTFw[w[x_]]:=w[x];
eTFw[0]:=0;
eTFw[0.]:=0;
(*w\[Rule]e*)
wTFe[x_+y_]:=wTFe[x]+wTFe[y];
wTFe[a_ e[x_]]:=Expand[a e[x]];
wTFe[a_ w[x_]]:=Expand[a wTFe[w[x]]];

wTFe[w[S_]]:=If[Count[S,0]>0 && Count[S,\[Infinity]]>0,
 e[S]+(-1)^Length[S] *e[Complement[S,{0,\[Infinity]}]], e[S]];

wTFe[e[x_]]:=e[x];
wTFe[0]:=0;
wTFe[0.]:=0;


(* ::Text:: *)
(*eTFw , wTFe\:306e\:8aac\:660e*)


eTFw::usage="eTFw[e[x]] CGA\:306e\:7a4d\:3067\:4f5c\:6210\:3057\:305f\:57fa\:5e95e\:3092,\:5916\:7a4d\:3067\:4f5c\:6210\:3057\:305f\:57fa\:5e95w\:306b\:53d6\:308a\:66ff\:3048\:308b.";
wTFe::usage="wTFe[w[x]] CGA\:306e\:5916\:7a4d\:3067\:4f5c\:6210\:3057\:305f\:57fa\:5e95w\:3092,\:7a4d\:3067\:4f5c\:6210\:3057\:305f\:57fa\:5e95e\:306b\:53d6\:308a\:66ff\:3048\:308b.";


(* ::Text:: *)
(*\:8a18\:53f7\:306e\:5b9a\:7fa9*)


(*\:8a08\:7b97\:306e\:5b9a\:7fa9*)
(*Reversion:\:9006\:9806*)
Reversion[x_+y_]:=Collect[(Reversion[Expand[x]]+Reversion[Expand[y]]),w[_],Simplify];
Reversion[a_ w[x_]]:=a Reversion[w[x]];
Reversion[w[x_]]:=(-1)^(Length[x]*(Length[x]-1)/2) w[x];

(* Involution: Conjugation:\:5171\:5f79 Inversion:\:9006\:5143 *)

(*\:8a18\:53f7\:306e\:5b9a\:7fa9*)
(*CGA\:306e\:5143*)
CGA[x_]:=Module[{L=Length[x],bases={},i},For[i=0,i<L-1,i++,bases=Join[bases,{w[{i}]}]];bases=Join[bases,{w[{\[Infinity]}]}];x.bases];


(*\:30b9\:30ab\:30e9\:30fc:Scalar*)
Sca[k_]:=k w[{}];
(*\:30d9\:30af\:30c8\:30eb:Vector*)
Vec[x_]:=Module[{L=Length[x],bases={},i},For[i=1,i<=L,i++,bases=Join[bases,{w[{i}]}]];x.bases];
(*\:4e8c\:91cd\:30d9\:30af\:30c8\:30eb:Bivector*)
Biv[a_,b_]:=OuterProduct[Vec[a],Vec[b]];
(*\:4e09\:91cd\:30d9\:30af\:30c8\:30eb:Trivector*)
Tri[a_,b_,c_]:=OuterProduct[OuterProduct[Vec[a],Vec[b]],Vec[c]];

(*\:70b9:Point*)
Pnt[x_]:=w[{0}]+Vec[x]+(x.x)/2 w[{\[Infinity]}];
(*\:865a\:6570\:70b9?:\:5927\:304d\:3055\:304c\:8ca0*)
ImPnt[x_]:=w[{0}]+Vec[x]-(x.x)/2 w[{\[Infinity]}];
(*\:70b9\:306e\:6b63\:898f\:5316:w[{0}]\:306e\:4fc2\:6570=1*)
NPnt[P_]:=Collect[eTFw[Expand[(1/Coefficient[P,w[{0}]] P)]],w[_],Simplify];
(*\:30dd\:30a4\:30f3\:30c8\:30da\:30a2:PointPair*)
Par[Pa_,Pb_]:=OuterProduct[Pnt[Pa],Pnt[Pb]];
(*\:5186:Circle*)
Cir[Pa_,Pb_,Pc_]:=OuterProduct[OuterProduct[Pnt[Pa],Pnt[Pb]],Pnt[Pc]];
(*\:7403:Sphere*)
Sph[Pa_,Pb_,Pc_,Pd_]:=OuterProduct[OuterProduct[OuterProduct[Pnt[Pa],Pnt[Pb]],Pnt[Pc]],Pnt[Pd]];
(*\:6c34\:5e73\:70b9:FlatPoint*)
Flp[Pa_]:=OuterProduct[Pnt[Pa],w[{\[Infinity]}]];

(*\:76f4\:7dda:Line*)
Lin[Pa_,Pb_]:=OuterProduct[OuterProduct[Pnt[Pa],Pnt[Pb]],w[{\[Infinity]}]];
(*\:53cc\:5bfe\:76f4\:7dda:DualLine*)
Dll[a_,b_,x_]:=Biv[a,b]+Drv[x];
(*\:5e73\:9762:Plane*)
Pln[Pa_,Pb_,Pc_]:=OuterProduct[OuterProduct[OuterProduct[Pnt[Pa],Pnt[Pb]],Pnt[Pc]],w[{\[Infinity]}]];
(*\:53cc\:5bfe\:5e73\:9762:DualPlane*)
Dlp[x_,s_]:=Vec[x]+s w[{\[Infinity]}];


(*\:65b9\:5411\:30d9\:30af\:30c8\:30eb:DirectionVector*)
Drv[x_]:=CGAProduct[Vec[x],w[{\[Infinity]}]];
(*\:65b9\:5411\:4e8c\:91cd\:30d9\:30af\:30c8\:30eb:DirectionBivector*)
Drb[a_,b_]:=CGAProduct[Biv[a,b],w[{\[Infinity]}]];
(*\:65b9\:5411\:4e09\:91cd\:30d9\:30af\:30c8\:30eb:DirectionTrivector*)
Drt[a_,b_,c_]:=CGAProduct[Tri[a,b,c],w[{\[Infinity]}]];

(*\:63a5\:7dda\:30d9\:30af\:30c8\:30eb:TangentVector*)
Tnv[x_]:=CGAProduct[w[{0}],Vec[x]];
(*\:63a5\:7dda\:4e8c\:91cd\:30d9\:30af\:30c8\:30eb:TangentBivector*)
Tnb[a_,b_]:=CGAProduct[w[{0}],Biv[a,b]];
(*\:63a5\:7dda\:4e09\:91cd\:30d9\:30af\:30c8\:30eb:TangentTrivector*)
Tnt[a_,b_,c_]:=CGAProduct[w[{0}],Tri[a,b,c]];


(*\:30df\:30f3\:30b3\:30d5\:30b9\:30ad\:30fc\:5e73\:9762:MinkowskiPlane*)
Mnk:=OuterProduct[w[{0}],w[{\[Infinity]}]];
(*\:64ec\:30b9\:30ab\:30e9\:30fc:Pseudoscalar*)
Pss:=-w[{0,1,2,3,\[Infinity]}];
(*\:7121\:9650\:9060\:70b9:Infinity*)
Inf:=w[{\[Infinity]}];


(* ::Text:: *)
(*\:5909\:63db\:8a18\:53f7\:306e\:5b9a\:7fa9*)


(*\:5e73\:884c\:79fb\:52d5:Translator, d:\:30d9\:30af\:30c8\:30eb*)
Trs[d_]:=w[{}]-1/2*CGAProduct[d,w[{\[Infinity]}]];
TrsI[d_]:=w[{}]+1/2*CGAProduct[d,w[{\[Infinity]}]];
Translator[x_,d_]:=Collect[Expand[CGAProduct[Trs[d],CGAProduct[x,TrsI[d]]]],w[_],Simplify];
(*B\:4e0a\:3067\:306e\[Theta]\:56de\:8ee2:Rotor, B:Bivector,\[Theta]:\:56de\:8ee2\:89d2*)
Rot[B_,\[Theta]_]:=Cos[\[Theta]/2] w[{}]-Sin[\[Theta]/2] B;
RotI[B_,\[Theta]_]:=Cos[\[Theta]/2] w[{}]+Sin[\[Theta]/2] B;
Rotor[x_,B_,\[Theta]_]:=CGAProduct[Rot[B,\[Theta]],CGAProduct[x,RotI[B,\[Theta]]]];
(*\:62e1\:5927:Dilator, \[Lambda]:e^\[Lambda]\:500d\:3059\:308b*)
Dil[\[Lambda]_]:=Cosh[\[Lambda]/2] w[{}]+Sinh[\[Lambda]/2] Mnk;
DilI[\[Lambda]_]:=Cosh[\[Lambda]/2] w[{}]-Sinh[\[Lambda]/2] Mnk;
Dilator[x_,\[Lambda]_]:=CGAProduct[Dil[\[Lambda]],CGAProduct[x,DilI[\[Lambda]]]];



(*\:93e1\:6620:Reflector, n:\:5358\:4f4d\:6cd5\:7dda\:30d9\:30af\:30c8\:30eb,h:\:539f\:70b9\:304b\:3089\:306e\:5e73\:9762\:306e\:8ddd\:96e2*)
Ref[n_,h_]:= n + h w[{\[Infinity]}];
Reflector[x_,n_,h_]:=- CGAProduct[Ref[n,h],x,Ref[n,h]];
(*\:53cd\:8ee2:Inversion,c:\:4e2d\:5fc3\:70b9Pnt,r:\:534a\:5f84*)
Inv[c_,r_]:=c-(r*r)/2 *CGAProduct[w[{}],w[{\[Infinity]}]];
Inversion[x_,c_,r_]:=- CGAProduct[Inv[c,r],x,Inv[c,r]];


Translator::usage="Translator[x,d] CGA\:4e0a\:306e\:5143x\:3092,CGA\:4e0a\:306e\:30d9\:30af\:30c8\:30ebd\:3067\:5e73\:884c\:79fb\:52d5.";
Rotor::usage="Rotor[x,B,\[Theta]] CGA\:4e0a\:306e\:5143x\:3092,CGA\:4e0a\:306e\:4e8c\:91cd\:30d9\:30af\:30c8\:30ebB\:3067\:5f35\:308b\:5e73\:9762\:4e0a\:3067\[Theta]\:56de\:8ee2.";
Dilator::usage="Dilator[x,\[Lambda]] CGA\:4e0a\:306e\:5143x\:3092,e^\[Lambda]\:500d\:306b\:62e1\:5927.";


(* ::Text:: *)
(*\:8a18\:53f7\:306e\:8aac\:660e*)


CGA::usage="CGA[x] 1-vector\:306e\:5404\:6210\:5206\:3092\:30d9\:30af\:30c8\:30ebx\:3067\:5165\:529b\:3059\:308b\:3068,CGA\:306e\:5143\:3067\:8868\:793a.";
Sca::usage="Sca[k] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30b9\:30ab\:30e9\:30fck\:3092,CGA\:4e0a\:306e\:30b9\:30ab\:30e9\:30fc\:306b\:5909\:63db.";
Vec::usage="Vec[x] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx\:3092,CGA\:4e0a\:306e\:30d9\:30af\:30c8\:30eb\:306b\:5909\:63db.";
Biv::usage="Biv[x,y] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx,y\:304b\:3089,CGA\:4e0a\:306e\:4e8c\:91cd\:30d9\:30af\:30c8\:30eb\:3092\:4f5c\:6210.";
Tri::usage="Tri[x,y,z] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx,y,z\:304b\:3089,CGA\:4e0a\:306e\:4e09\:91cd\:30d9\:30af\:30c8\:30eb\:3092\:4f5c\:6210.";
Pnt::usage="Pnt[x] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:70b9x\:3092,CGA\:4e0a\:306e\:70b9\:306b\:5909\:63db.";
ImPnt::usage="ImPnt[x] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:70b9x\:304b\:3089,CGA\:4e0a\:306e\:865a\:6570\:70b9\:3092\:4f5c\:6210.";
NPnt::usage="NPnt[P] CGA\:4e0a\:306e\:70b9P\:3092\:6b63\:898f\:5316.";
Par::usage="Par[x,y] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:ff12\:70b9x,y\:3092,CGA\:4e0a\:306e\:70b9\:306e\:7d44\:306b\:5909\:63db.";
Cir::usage="Cir[x,y,z] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:ff13\:70b9x,y,z\:3092\:901a\:308b\:5186\:3092\:4f5c\:6210.";
Sph::usage="Sph[x,y,z,w] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:ff14\:70b9x,y,z,w\:3092\:901a\:308b\:7403\:3092\:4f5c\:6210.";
Flp::usage="Flp[x] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:70b9x\:304b\:3089,CGA\:4e0a\:306e\:6c34\:5e73\:70b9\:3092\:4f5c\:6210.";
Lin::usage="Lin[x,y] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:ff12\:70b9x,y\:3092\:901a\:308b\:76f4\:7dda\:3092\:4f5c\:6210.";
Dll::usage="Dll[a,b,x] \:4e8c\:91cd\:30d9\:30af\:30c8\:30ebBiv[a,b]\:3068\:65b9\:5411\:30d9\:30af\:30c8\:30ebDrv[x]\:306e\:548c.";
Pln::usage="Pln[x,y,z] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:ff13\:70b9x,y,z\:3092\:901a\:308b\:5e73\:9762\:3092\:4f5c\:6210.";
Dlp::usage="Dlp[x,s] \:30d9\:30af\:30c8\:30ebVec[x]\:3068s w[{\[Infinity]}]\:306e\:548c(s\:306f\:30b9\:30ab\:30e9\:30fc\:500d).";
Mnk::usage="Mnk \:30df\:30f3\:30b3\:30d5\:30b9\:30ad\:30fc\:5e73\:9762\:3092\:5b9a\:7fa9.";
Drv::usage="Drv[x] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx\:304b\:3089,CGA\:4e0a\:306e\:65b9\:5411\:30d9\:30af\:30c8\:30eb\:3092\:4f5c\:6210.";
Drb::usage="Drb[x,y] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx,y\:304b\:3089,CGA\:4e0a\:306e\:65b9\:5411\:4e8c\:91cd\:30d9\:30af\:30c8\:30eb\:3092\:4f5c\:6210.";
Drt::usage="Drt[x,y,z] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx,y,z\:304b\:3089,CGA\:4e0a\:306e\:65b9\:5411\:4e09\:91cd\:30d9\:30af\:30c8\:30eb\:3092\:4f5c\:6210.";
Tnv::usage="Tnv[x] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx\:304b\:3089,CGA\:4e0a\:306e\:63a5\:7dda\:30d9\:30af\:30c8\:30eb\:3092\:4f5c\:6210.";
Tnb::usage="Tnb[x,y] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx,y\:304b\:3089,CGA\:4e0a\:306e\:63a5\:7dda\:4e8c\:91cd\:30d9\:30af\:30c8\:30eb\:3092\:4f5c\:6210.";
Tnt::usage="Tnt[x,y,z] \:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:306e\:30d9\:30af\:30c8\:30ebx,y,z\:304b\:3089,CGA\:4e0a\:306e\:63a5\:7dda\:4e09\:91cd\:30d9\:30af\:30c8\:30eb\:3092\:4f5c\:6210.";

Trs::usage="Trs[d] CGA\:306e\:30d9\:30af\:30c8\:30ebd\:304b\:3089,\:5e73\:884c\:79fb\:52d5\:5b50\:3092\:4f5c\:6210.";
Rot::usage="Rot[B,\[Theta]] \:4e8c\:91cd\:30d9\:30af\:30c8\:30ebB(\:56de\:8ee2\:9762)\:3068\:56de\:8ee2\:89d2\:5ea6\[Theta]\:304b\:3089, \:56de\:8ee2\:5b50\:3092\:4f5c\:6210.";
Dil::usage="Dil[\[Lambda]] \:5b9f\:6570\[Lambda]\:304b\:3089, \:62e1\:5927(\:7e2e\:5c0f)\:5b50\:3092\:4f5c\:6210(e^\[Lambda]\:500d).";
Ref::usage="Ref[n,h] \:5883\:754c\:9762\:306e\:539f\:70b9\:304b\:3089\:306e\:8ddd\:96e2h\:3068\:5358\:4f4d\:6cd5\:7dda\:30d9\:30af\:30c8\:30ebn\:3068\:3059\:308b,\:93e1\:6620\:5b50\:3092\:4f5c\:6210.";
Inv::usage="Inv[c,h] CGA\:306e\:70b9c\:3092\:4e2d\:5fc3\:3068\:3057\:305f\:534a\:5f84r\:306e,\:53cd\:8ee2\:5b50\:3092\:4f5c\:6210.";



myInner[x_+y_,z_]:=myInner[x,z]+myInner[y,z];
myInner[x_,y_+z_]:=myInner[x,y]+myInner[x, z];
myInner[a_ w[x_],w[y_]]:=a myInner[w[x],w[y]];
myInner[w[x_],a_ w[y_]]:=a myInner[w[x], w[y]];
myInner[b_ w[x_],a_ w[y_]]:=a b myInner[w[x], w[y]];
myInner[x_,0]:=0;
myInner[0,y_]:=0;
myInner[w[x_],w[y_]]:=If[x==y,1,0,0]
myNorm[x_,y_]:=Collect[Expand[myInner[x,x]],y,Simplify];
myNorm[x_]:=myInner[x,x];


(* ::Text:: *)
(*CGA\:306e\:8868\:793a*)


LineContour[X_,{x_,y_,z_},{xm_,xM_},{ym_,yM_},{zm_,zM_},opts:OptionsPattern[]]:=
If[Length[Solve[X==0,{y,z}]]==0,
	If[Length[Solve[X==0,{x,z}]]==0,
		ParametricPlot3D[{x,y,z}/.Solve[X==0,{x,y},Reals],{z,zm,zM},PlotRange->{{xm,xM},{ym,yM},{zm,zM}},opts],
		ParametricPlot3D[{x,y,z}/.Solve[X==0,{x,z},Reals],{y,ym,yM},PlotRange->{{xm,xM},{ym,yM},{zm,zM}},opts]
	],
	ParametricPlot3D[{x,y,z}/.Solve[X==0,{y,z},Reals],{x,xm,xM},PlotRange->{{xm,xM},{ym,yM},{zm,zM}},opts]
];
(*X\[Equal]0\:3068\:306a\:308b\:7dda\:307e\:305f\:306f\:5186\:3092\:51fa\:529b\:3059\:308b\:3002{x_,y_,z_}\:306fX\:3067\:4f7f\:308f\:308c\:3066\:3044\:308b\:6587\:5b57\:306e\:96c6\:5408
{xm_,xM_},{ym_,yM_},{zm_,zM_}\:306f\:8868\:793a\:7bc4\:56f2
\:5186\:306e\:8868\:793a\:306f\:6642\:9593\:304c\:304b\:304b\:308b*)

CGAOutput3D[AlgebraicForm_,{{xm_,xM_},{ym_,yM_},{zm_,zM_}},opts:OptionsPattern[]]:=
Module[{Outer,CGACoef,x,y,z},
	Outer=OuterProduct[AlgebraicForm,Pnt[{x,y,z}]];(*OuterProdution\:3092\:3068\:308b*)
	CGACoef=CoefPickUp[Outer];(*\:4fc2\:6570\:3092\:66f8\:304d\:51fa\:3059*)
	CGACoef=GroebnerBasis[CGACoef,{x,y,z}];(*\:4fc2\:6570\:306e\:30b0\:30ec\:30d6\:30ca\:57fa\:5e95\:3092\:6c42\:3081\:308b*)
	Switch[Length[CGACoef],(*\:57fa\:5e95\:306e\:6570\:3067\:5834\:5408\:5206\:3051*)
		3,ListPointPlot3D[{x,y,z}/.Solve[CGACoef==0,{x,y,z}],PlotRange->{{xm,xM},{ym,yM},{zm,zM}},opts](*\:89e3\:3092Plot*),
		2,LineContour[CGACoef,{x,y,z},{xm,xM},{ym,yM},{zm,zM},opts](*LineContour\:3092\:65b0\:3057\:304f\:5b9a\:7fa9\:3057\:305f*),
		1,ContourPlot3D[CGACoef[[1]]==0,{x,xm,xM},{y,ym,yM},{z,zm,zM},opts](*\:4fc2\:6570==0\:3092Plot*),
		_,0
	]
];
(*AlgebraicForm_\:3092\:8868\:793a\:3059\:308b\:95a2\:6570\:3002{xm_,xM_},{ym_,yM_},{zm_,zM_}\:306f\:8868\:793a\:7bc4\:56f2*)

CGADualOutput3D[AlgebraicForm_,{{xm_,xM_},{ym_,yM_},{zm_,zM_}}]:=
Module[{Inner,CGACoef,x,y,z},
	Inner=InnerProduct[AlgebraicForm,Pnt[{x,y,z}]];(*OuterProdution\:3092\:3068\:308b*)
	CGACoef=CoefPickUp[Inner];(*\:4fc2\:6570\:3092\:66f8\:304d\:51fa\:3059*)
	CGACoef=GroebnerBasis[CGACoef,{x,y,z}];(*\:4fc2\:6570\:306e\:30b0\:30ec\:30d6\:30ca\:57fa\:5e95\:3092\:6c42\:3081\:308b*)
	Switch[Length[CGACoef],(*\:57fa\:5e95\:306e\:6570\:3067\:5834\:5408\:5206\:3051*)
		3,ListPointPlot3D[{x,y,z}/.Solve[CGACoef==0,{x,y,z}](*\:89e3\:3092Plot*),PlotRange->{{xm,xM},{ym,yM},{zm,zM}}],
		2,LineContour[CGACoef,{x,y,z},{xm,xM},{ym,yM},{zm,zM}](*LineContour\:3092\:65b0\:3057\:304f\:5b9a\:7fa9\:3057\:305f*),
		1,ContourPlot3D[CGACoef[[1]]==0,{x,xm,xM},{y,ym,yM},{z,zm,zM}](*\:4fc2\:6570==0\:3092Plot*),
		_,0
	]
];
(*AlgebraicForm_\:3092\:8868\:793a\:3059\:308b\:95a2\:6570(Dual\:3092\:8868\:793a)\:3002{xm_,xM_},{ym_,yM_},{zm_,zM_}\:306f\:8868\:793a\:7bc4\:56f2*)


CGAOutput2D[AlgebraicForm_,{{xm_,xM_},{ym_,yM_}},opts:OptionsPattern[]]:=
Module[{graph,Outer,CGACoef,x,y},
Outer=OuterProduct[AlgebraicForm,Pnt[{x,y}]];(*OuterProdution\:3092\:3068\:308b*)
CGACoef=CoefPickUp[Outer];(*\:4fc2\:6570\:3092\:66f8\:304d\:51fa\:3059*)
CGACoef=GroebnerBasis[CGACoef,{x,y}];(*\:4fc2\:6570\:306e\:30b0\:30ec\:30d6\:30ca\:57fa\:5e95\:3092\:6c42\:3081\:308b*)
Switch[Length[CGACoef],(*\:57fa\:5e95\:306e\:6570\:3067\:5834\:5408\:5206\:3051*)
2,graph=Show[ContourPlot[0==0,{x,xm,xM},{y,ym,yM},opts](*\:67a0\:3092\:3042\:308f\:305b\:308b*),
	ListPlot[{x,y}/.Solve[CGACoef==0,{x,y}],PlotRange->{{xm,xM},{ym,yM}},opts]](*\:89e3\:3092Plot*),
1,graph=ContourPlot[CGACoef[[1]]==0,{x,xm,xM},{y,ym,yM},opts](*\:4fc2\:6570==0\:3092Plot*),
_,0
]
];


CGAOutput2D::usage="CGAOutput2D[AlgebraicForm,{{xm,xM},{ym,yM}}] 
CGA\:4e0a\:306e\:5143AlgebraicForm\:3092
,\:7bc4\:56f2{{xm,xM},{ym,yM}}\:30672D\:8868\:793a\:3059\:308b\:3002";
CGAOutput3D::usage="CGAOutput3D[AlgebraicForm,{{xm,xM},{ym,yM},{zm,zM}}] 
CGA\:4e0a\:306e\:5143AlgebraicForm\:3092
,\:7bc4\:56f2{{xm,xM},{ym,yM},{zm,zM}}\:30673D\:8868\:793a\:3059\:308b\:3002";
CGADualOutput3D::usage="CGADualOutput3D[AlgebraicForm,{{xm,xM},{ym,yM},{zm,zM}}] 
CGA\:4e0a\:306e\:5143AlgebraicForm\:3092Dual\:3067
,\:7bc4\:56f2{{xm,xM},{ym,yM},{zm,zM}}\:30673D\:8868\:793a\:3059\:308b\:3002";


(* ::Text:: *)
(*\:4e8c\:91cd\:8907\:7d20\:6570*)


Com[a_,b_]:=a w[{}]+CGAProduct[b w[{}],w[{1,2}]];(*\:8907\:7d20\:6570;\[ImaginaryI]=Subscript[w, 12]*)
DC1[a_,b_,\[Theta]_]:=Com[Cos[\[Theta]],Sin[\[Theta]]]+CGAProduct[Com[a,b],w[{0}]];(*\[Epsilon]=Subscript[w, 0];Subscript[w, 0]^2=0*)
DC2[x_,y_]:=w[{}]+CGAProduct[Com[x,y],w[{0}]];(*\[Epsilon]=Subscript[w, 0];Subscript[w, 0]^2=0*)
DC[x_,y_,a_,b_,\[Theta]_]:=CGAProduct[DC1[a,b,\[Theta]],DC2[x,y]]-Com[Cos[\[Theta]],Sin[\[Theta]]];


Com::usage="Com[a,b] \:8907\:7d20\:6570a+b\[ImaginaryI](a,b:\:30b9\:30ab\:30e9\:30fc,\:865a\:6570\[ImaginaryI]=\!\(\*SubscriptBox[\(w\), \(12\)]\).";
DC::usage="DC[x,y,a,b,\[Theta]] \:70b9{x,y}\:3092\[Theta]\:56de\:8ee2\:3057\:3066,{a,b}\:3060\:3051\:5e73\:884c\:79fb\:52d5\:3059\:308b.
x'\!\(\*SubscriptBox[\(w\), \(0\)]\)+y'\!\(\*SubscriptBox[\(w\), \(012\)]\)\:3092\:8868\:793a.";


(* ::Text:: *)
(*CGA\:306e\:4ea4\:70b9*)


CGAIntersection[A_,B_]:=
Module[{Outer1,CGACoef1,Outer2,CGACoef2,x,y,z},
	Outer1=OuterProduct[A,Pnt[{x,y,z}]];(*\:5916\:7a4d\:3092\:3068\:308b*)
	CGACoef1=CoefPickUp[Outer1];(*\:4fc2\:6570\:3092\:66f8\:304d\:51fa\:3059*)
	CGACoef1=GroebnerBasis[CGACoef1,{x,y,z}];(*\:4fc2\:6570\:306e\:30b0\:30ec\:30d6\:30ca\:57fa\:5e95\:3092\:6c42\:3081\:308b*)
Outer2=OuterProduct[B,Pnt[{x,y,z}]];(*\:5916\:7a4d\:3092\:3068\:308b*)
CGACoef2=CoefPickUp[Outer2];(*\:4fc2\:6570\:3092\:66f8\:304d\:51fa\:3059*)
CGACoef2=GroebnerBasis[CGACoef2,{x,y,z}];(*\:4fc2\:6570\:306e\:30b0\:30ec\:30d6\:30ca\:57fa\:5e95\:3092\:6c42\:3081\:308b*)
	{x,y,z}/.Solve[CGACoef1==0&&CGACoef2==0,{x,y,z}](*\:4ea4\:70b9\:3092\:6c42\:3081\:308b*)
];


CGAIntersection::usage="CGAIntersection[A,B] CGA\:4e0a\:306e\:5143A\:3068B\:306e\:30e6\:30fc\:30af\:30ea\:30c3\:30c9\:7a7a\:9593\:4e0a\:3067\:306e\:4ea4\:70b9\:3092\:6c42\:3081\:308b.";


(* ::Text:: *)
(*\:7b49\:4fa1\:6027\:5224\:5b9a*)


CGAEquationCheck[AlgebraicForm1_,AlgebraicForm2_]:=Module[{x,y,z,Outer1,Outer2,Coef1,Coef2},
Outer1=OuterProduct[AlgebraicForm1,Pnt[{x,y,z}]];
Outer2=OuterProduct[AlgebraicForm2,Pnt[{x,y,z}]];
Coef1=CoefPickUp[Outer1];
Coef2=CoefPickUp[Outer2];
Coef1=GroebnerBasis[Coef1,{x,y,z}];
Coef2=GroebnerBasis[Coef2,{x,y,z}];
If[Length[Coef1]==3&&Length[Coef2]==3,
Norm[Coef2/.Solve[Coef1==0,{x,y,z}]]==0&&Norm[Coef1/.Solve[Coef2==0,{x,y,z}]]==0,
Norm[PolynomialMod[Coef2,Coef1]]===0&&0===Norm[PolynomialMod[Coef1,Coef2]]
]
];


CGAEquationCheck::usage="CGAEquationCheck[A,B] CGA\:4e0a\:306e\:5143A\:3068B\:304c3\:6b21\:5143\:7a7a\:9593\:5185\:3067\:540c\:4e00\:306e\:70b9\:3067\:3042\:308b\:304b\:3069\:3046\:304b\:3092\:5224\:5b9a\:3059\:308b.";


(* ::Text:: *)
(*\:7dda\:5206*)


SegOutput2D[P1_,P2_,opts:OptionsPattern[]]:=
Module[{xm,xM,ym,yM,Pa,Pb},Pa=NPnt[P1];Pb=NPnt[P2];
If[Coefficient[Pa,w[{1}]]<Coefficient[Pb,w[{1}]],
(*Pb\:306ex\:5ea7\:6a19\:304c\:5927*)xm=Coefficient[Pa,w[{1}]];xM=Coefficient[Pb,w[{1}]],
If[Coefficient[Pa,w[{1}]]==Coefficient[Pb,w[{1}]],
(*x\:5ea7\:6a19\:304c\:7b49\:3057\:3044*)xm=Coefficient[Pa,w[{1}]]-1;xM=Coefficient[Pb,w[{1}]]+1,
(*Pa\:306ex\:5ea7\:6a19\:304c\:5927*)xm=Coefficient[Pb,w[{1}]];xM=Coefficient[Pa,w[{1}]] ] ];

If[Coefficient[Pa,w[{2}]]<Coefficient[Pb,w[{2}]],
(*Pb\:306ey\:5ea7\:6a19\:304c\:5927*)ym=Coefficient[Pa,w[{2}]];yM=Coefficient[Pb,w[{2}]],
If[Coefficient[Pa,w[{2}]]==Coefficient[Pb,w[{2}]],
(*y\:5ea7\:6a19\:304c\:7b49\:3057\:3044*)ym=Coefficient[Pa,w[{2}]]-1;yM=Coefficient[Pb,w[{2}]]+1,
(*Pa\:306ey\:5ea7\:6a19\:304c\:5927*)ym=Coefficient[Pb,w[{2}]];yM=Coefficient[Pa,w[{2}]] ] ];

CGAOutput2D[OuterProduct[Pa,Pb,w[{\[Infinity]}]],{{xm,xM},{ym,yM}},opts] ];


SegOutput3D[P1_,P2_]:=
Module[{xm,xM,ym,yM,zm,zM,Pa,Pb},Pa=NPnt[P1];Pb=NPnt[P2];
If[Coefficient[Pa,w[{1}]]<Coefficient[Pb,w[{1}]],
xm=Coefficient[Pa,w[{1}]];xM=Coefficient[Pb,w[{1}]],
xm=Coefficient[Pb,w[{1}]];xM=Coefficient[Pa,w[{1}]]  ];
If[Coefficient[Pa,w[{2}]]<Coefficient[Pb,w[{2}]],
ym=Coefficient[Pa,w[{2}]];yM=Coefficient[Pb,w[{2}]],
ym=Coefficient[Pb,w[{2}]];yM=Coefficient[Pa,w[{2}]]  ];
If[Coefficient[Pa,w[{3}]]<Coefficient[Pb,w[{3}]],
zm=Coefficient[Pa,w[{3}]];zM=Coefficient[Pb,w[{3}]],
zm=Coefficient[Pb,w[{3}]];zM=Coefficient[Pa,w[{3}]]  ];
	CGAOutput3D[OuterProduct[Pa,Pb,w[{\[Infinity]}]],{{xm,xM},{ym,yM},{zm,zM}}] ];


SegOutput2D::usage="SegOutput2D[P1,P2] CGA\:4e0a\:306e\:70b9P1\:304b\:3089P2\:306e\:7dda\:5206\:30922D\:8868\:793a\:3059\:308b\:3002";
SegOutput3D::usage="SegOutput3D[P1,P2] CGA\:4e0a\:306e\:70b9P1\:304b\:3089P2\:306e\:7dda\:5206\:30923D\:8868\:793a\:3059\:308b\:3002";


(* ::Text:: *)
(*\:95a2\:6570F\:306e\:5b9a\:7fa9*)
(*0:Rot    1:Trs*)


(*\:95a2\:6570F\:306e\:5b9a\:7fa9*)
Clear[T,R,F];
T[d_,a_]:=CGAProduct[a w[{}],Trs[d]];
R[B_,\[Theta]_,a_]:=CGAProduct[(1-a) w[{}],Rot[B,\[Theta]]];
F[x_,d_,B_,\[Theta]_,a_]:=Collect[Expand[
CGAProduct[(T[d,a]+R[B,\[Theta],a]),CGAProduct[x,Reversion[(T[d,a]+R[B,\[Theta],a]) ]]]
],w[_],Simplify];


F::usage="F[x_,d_,B_,\[Theta]_,a_]] CGA\:4e0a\:306e\:5143x\:3092,\:5e73\:884c\:79fb\:52d5a,\:56de\:8ee2(1-a)\:3067\:5408\:6210.
\:30d9\:30af\:30c8\:30ebd\:3067\:5e73\:884c\:79fb\:52d5,\:4e8c\:91cd\:30d9\:30af\:30c8\:30ebB\:3067\:5f35\:308b\:5e73\:9762\:4e0a\:3067\[Theta]\:56de\:8ee2.";


(* ::Text:: *)
(*CGA\:306e\:70b9\:30923D, 2D\:306e\:30d9\:30af\:30c8\:30eb\:306b\:3059\:308b*)


RPnt3D[x_]:=Module[{Out,a,b,c,CGACoef},
Out=OuterProduct[x,Pnt[{a,b,c}]];(*\:5916\:7a4d\:3092\:3068\:308b*)
CGACoef=CoefPickUp[Out];(*\:4fc2\:6570\:3092\:66f8\:304d\:51fa\:3059*)
CGACoef=GroebnerBasis[CGACoef,{a,b,c}];(*\:4fc2\:6570\:306e\:30b0\:30ec\:30d6\:30ca\:57fa\:5e95\:3092\:6c42\:3081\:308b*)
({a,b,c}/.Solve[CGACoef==0,{a,b,c}])[[1]](*//Flatten\:3067\:3082\:53ef\:ff1f*)
];
RPnt2D[x_]:=Module[{Out,a,b,CGACoef},
Out=OuterProduct[x,Pnt[{a,b}]];
CGACoef=CoefPickUp[Out];
{a,b}/.Solve[CGACoef==0,{a,b}]
];


RPnt3D::usage="RPnt3D[x_] CGA\:4e0a\:306e\:70b9x\:30923D\:306e\:70b9\:306b\:3059\:308b.";
RPnt2D::usage="RPnt2D[x_] CGA\:4e0a\:306e\:70b9x\:30922D\:306e\:70b9\:306b\:3059\:308b.";


(* ::Text:: *)
(*\:9006\:5143\:306e\:8a08\:7b97*)


eInversion[AlgebraicForm_]:=Module[{eBaseForm,CoefList1,BaseInversion,Inver},
BaseInversion[subset_]:=CGAProduct[Map[e[{#}]&,Reverse[subset]]];
eBaseForm=Collect[wTFe[AlgebraicForm],e[_]];
CoefList1=Association[Map[{#->Coefficient[eBaseForm,e[#]]}&,Subsets[{0,1,2,3,\[Infinity]}]]];
CoefList1=KeyDrop[CoefList1,Select[Keys[CoefList1],CoefList1[#]==0&]];
Inver=Collect[eTFw[Expand[Total[Map[CoefList1[#] BaseInversion[#]&,Keys[CoefList1]]]]],w[_]];
Return[Inver];
];


eInversion::usage="eInversion[AlgebraicForm_] e[{a,b,c}]->e[{c,b,a}]\:306b\:3059\:308b.";


CGAInverse[AlgebraicForm_]:=Module[{element1,element2,element3,element4,element5,element6,element7,denominator0,element8},
element1=wTFe[Expand[AlgebraicForm]];
element2=Collect[wTFe[eInversion[element1]],e[_]];
element3=wTFe[CGAProduct[element1,element2]];
element4=
Collect[
2 Coefficient[element3,e[{}]]  e[{}]+2 Coefficient[element3,e[{1,2,3}]]  e[{1,2,3}]+2 Coefficient[element3,e[{0,1,2,3,\[Infinity]}]]  e[{0,1,2,3,\[Infinity]}]
-element3
,e[_]];
element5=wTFe[CGAProduct[element3,element4]];
element6=Coefficient[element5,e[{}]]e[{}]-Coefficient[element5,e[{1,2,3}]]e[{1,2,3}]-Coefficient[element5,e[{0,1,2,3,\[Infinity]}]]e[{0,1,2,3,\[Infinity]}];
element7=wTFe[CGAProduct[element5,element6]];
denominator0=Coefficient[element7,e[{}]];
If[Chop[denominator0]==0,Print[AlgebraicForm,"\:306b\:9006\:5143\:306f\:3042\:308a\:307e\:305b\:3093."] ;Return[]];
element8=CGAProduct[{1/denominator0 w[{}],eTFw[element2],eTFw[element4],eTFw[element6]}];
Return[element8];
];


CGAInverse::usage="CGAInverse[AlgebraicForm_] CGA\:306e\:5143 AlgebgaricForm \:306e\:9006\:5143.";


CGADeterminant[AlgebraicForm_]:=Module[{element1,element2,element3,element4,element5,element6,element7,denominator0},
element1=wTFe[Expand[AlgebraicForm]];
element2=Collect[wTFe[eInversion[element1]],e[_]];
element3=wTFe[CGAProduct[element1,element2]];
element4=
Collect[
2 Coefficient[element3,e[{}]]  e[{}]+2 Coefficient[element3,e[{1,2,3}]]  e[{1,2,3}]+2 Coefficient[element3,e[{0,1,2,3,\[Infinity]}]]  e[{0,1,2,3,\[Infinity]}]
-element3
,e[_]];
element5=wTFe[CGAProduct[element3,element4]];
element6=Coefficient[element5,e[{}]]e[{}]-Coefficient[element5,e[{1,2,3}]]e[{1,2,3}]-Coefficient[element5,e[{0,1,2,3,\[Infinity]}]]e[{0,1,2,3,\[Infinity]}];
element7=wTFe[CGAProduct[element5,element6]];
denominator0=Coefficient[element7,e[{}]];
Return[N[Surd[denominator0,8]]];
];


CGADeterminant::usage="CGADeterminant[AlgebraicForm_] CGA\:306e\:5143 AlgebgaricForm \:306e
Determinant\:3092\:8a08\:7b97\:3059\:308b. 0\:3067\:306a\:3044\:3068\:304d\:9006\:5143\:3092\:3082\:3064.";


(* ::Text:: *)
(*\:6298\:308a\:7d19\:3078\:306e\:5fdc\:7528*)


OriOperator[x_,y_,\[Theta]_]:=Module[{xx=y-x,NNN,Bi,R,T,TI,O,OI},
NNN=(CGAProduct[xx,xx]/.w[{}]->1);
xx=Collect[xx/N[Sqrt[NNN]],w[_]];(* xx=y-x \:3092\:5358\:4f4d\:30d9\:30af\:30c8\:30eb\:306b\:3059\:308b*)
Bi=CGAProduct[xx,-w[{1,2,3}]];(* y-x \:306e\:76f4\:884c\:88dc\:7a7a\:9593*)
R=Rot[Bi,\[Theta]];(* y-x \:306b\:5bfe\:3059\:308b \:5de6\:30cd\:30b8\:65b9\:5411\:306e\:56de\:8ee2*)
T=Trs[x]; (* \:30d9\:30af\:30c8\:30ebx\:65b9\:5411\:3078\:306e\:5e73\:884c\:79fb\:52d5 *)
TI=TrsI[x];
O=CGAProduct[{T,R,TI}];
O
];


OriOperator::usage="OriOperator[x_,y_,\[Theta]_] \:6709\:5411\:76f4\:7ddaxy(\:30d9\:30af\:30c8\:30ebx\:304b\:3089\:30d9\:30af\:30c8\:30eby\:3078)\:3092
\:3000\:6298\:308a\:7dda\:3068\:3057\:305f\:89d2\:5ea6\[Theta] \:306e\:6298\:308a\:64cd\:4f5c\:306e\:4f5c\:7528\:5b50.";


CGAOri3D[O_,Op_,C_]:=Append[O,
"P"->
Join[O["P"],Association[
Map[
#->{O["P"][#][[1]],CGAProduct[Op,O["P"][#][[2]]]}&,
Union[Flatten[Map[O["F"][#]&,C]]]]]
]
];


CGAOri3D::usage="CGAOri3D[O_,Op_,C_] \:6298\:308a\:7d19O \:306e\:9762\:96c6\:5408C \:306e\:5404\:9802\:70b9\:306b\:4f5c\:7528\:5b50Op \:3092\:4f5c\:7528\:3055\:305b\:308b.";


CGAPolygon[PointSet_]:=Polygon[Map[RPnt3D,PointSet]];
OrigamiPointCoodinate[O_,Pkey_]:=
CGAProduct[O["P"][Pkey][[2]],O["P"][Pkey][[1]],CGAInverse[O["P"][Pkey][[2]]]];
OrigamiFace[O_,Fkey_]:=<|Fkey->CGAPolygon[Map[OrigamiPointCoodinate[O,#]&,O["F"][Fkey]]]|>;
OrigamiFaceSet[O_]:=Association[Map[OrigamiFace[O,#]&,Keys[O["F"]]]];
OrigamiFacePolygons[O_]:=Prepend[Values[OrigamiFaceSet[O]],FaceForm[Yellow,Green]];
OrigamiFaceName[O_]:=
Map[Text[Style[Subscript["f", (#)],Large,Bold,Black],Total[OrigamiFaceSet[O][#][[1]]]/Length[OrigamiFaceSet[O][#][[1]]]]&,
Keys[OrigamiFaceSet[O]]];
OrigmiPointOutput[O_]:=Map[Text[Style[Subscript["P", (#)],Large,Bold,Red],RPnt3D[OrigamiPointCoodinate[O,#]]]&,Keys[O["P"]]];
OrigamiOutput[O_]:=OrigamiOutput[O,{}];
OrigamiOutput[O_,RRule_]:=Graphics3D[Join[OrigamiFaceName[O],OrigmiPointOutput[O],OrigamiFacePolygons[O]]/.RRule,Boxed->False];


CGAPolygon::usage="CGAPolygon[PointSet_] CGA\:306e\:70b9\:96c6\:5408\:304b\:3089, \:305d\:308c\:3092\:9802\:70b9\:3068\:3057\:305fPolygon\:3092\:4f5c\:308b.";
OrigamiPointCoodinate::usage="OrigamiPointCoodinate[O_,Pkey_] \:6298\:308a\:7d19O \:306e\:70b9Pkey \:3092\:8a08\:7b97\:3059\:308b.";
OrigamiFace::usage="OrigamiFace[O_,Fkey_] \:6298\:308a\:7d19O \:306e\:9762Fkey \:306ePolygon\:3092\:8a08\:7b97\:3059\:308b.";
OrigamiFaceSet::usage="OrigamiFaceSet[O_] \:6298\:308a\:7d19O \:306e\:3059\:3079\:3066\:306e\:9762 \:306ePolygon\:3092\:8a08\:7b97\:3059\:308b.";
OrigamiFaceOutput::usage="OrigamiFaceOutput[O_]\:3000OrigamiFaceOutput[O_,RRule_] \:6298\:308a\:7d19O \:306e\:3059\:3079\:3066\:306e\:9762\:3092\:8868\:793a.";
OrigamiFaceName::usage="OrigamiFaceName[O_]\:3000\:6298\:308a\:7d19O \:306e\:3059\:3079\:3066\:306e\:9762\:306e\:540d\:524d\:3092Text\:306b\:3059\:308b.";
OrigmiPointOutput::usage="OrigmiPointOutput[O_]\:3000\:6298\:308a\:7d19O \:306e\:3059\:3079\:3066\:306e\:9762\:306e\:540d\:524d\:3092Text\:306b\:3059\:308b.";


(* ::Text:: *)
(*\:30c7\:30e2\:7528\:753b\:50cf*)


Human0={
(*1*)Pnt[{70,8}],
(*2*)Pnt[{71,3}],
(*3*)Pnt[{58,0}],
(*4*)Pnt[{55,8}],
(*5*)Pnt[{80,5}],
(*6*)Pnt[{86,-5}],
(*7*)Pnt[{78,-18}],
(*8*)Pnt[{63,-8}],
(*9*)Pnt[{62,-18}],
(*10:C1*)Cir[{50,0},{90,0},{70,20}],
(*11:C2*)Cir[{65,13},{75,13},{70,18}],
(*12:P1*)Pnt[{50,0}],
(*13:P2*)Pnt[{90,0}]
};
HumanOutSet2D[X_,Range_,Col_]:=Module[{Out},
Out={
CGAOutput2D[X[[10]],Range,ContourStyle->Col] ,
CGAOutput2D[X[[11]],Range,ContourStyle->Col] ,

SegOutput2D[X[[1]],X[[2]],ContourStyle->Col],
SegOutput2D[X[[2]],X[[3]],ContourStyle->Col],
SegOutput2D[X[[3]],X[[4]],ContourStyle->Col],
SegOutput2D[X[[2]],X[[5]],ContourStyle->Col],
SegOutput2D[X[[5]],X[[6]],ContourStyle->Col],
SegOutput2D[X[[2]],X[[7]],ContourStyle->Col],
SegOutput2D[X[[2]],X[[8]],ContourStyle->Col],
SegOutput2D[X[[8]],X[[9]],ContourStyle->Col],

CGAOutput2D[X[[12]],Range,PlotStyle->Col],
CGAOutput2D[X[[13]],Range,PlotStyle->Col] 
} ];




House0={
(*1*)Pnt[{65,100}],
(*2*)Pnt[{20,60}],
(*3*)Pnt[{110,60}],
(*4*)Pnt[{35,60}],
(*5*)Pnt[{35,0}],
(*6*)Pnt[{95,0}],
(*7*)Pnt[{95,60}],

(*8*)Pnt[{80,0}],
(*9*)Pnt[{80,30}],
(*10*)Pnt[{90,30}],
(*11*)Pnt[{90,0}],
(*12:C1*)Cir[{86,15},{90,15},{88,17}],

(*13*)Pnt[{40,55}],
(*14*)Pnt[{40,25}],
(*15*)Pnt[{70,25}],
(*16*)Pnt[{70,55}],
(*17*)Pnt[{40,40}],
(*18*)Pnt[{70,40}],
(*19*)Pnt[{55,55}],
(*20*)Pnt[{55,25}]


};
HouseOutSet2D[X_,Range_,Col_]:=Module[{Out},
Out={
CGAOutput2D[X[[12]],Range,ContourStyle->Col] ,

SegOutput2D[X[[1]],X[[2]],ContourStyle->Col],
SegOutput2D[X[[2]],X[[3]],ContourStyle->Col],
SegOutput2D[X[[3]],X[[1]],ContourStyle->Col],

SegOutput2D[X[[4]],X[[5]],ContourStyle->Col],
SegOutput2D[X[[5]],X[[6]],ContourStyle->Col],
SegOutput2D[X[[6]],X[[7]],ContourStyle->Col],

SegOutput2D[X[[8]],X[[9]],ContourStyle->Col],
SegOutput2D[X[[9]],X[[10]],ContourStyle->Col],
SegOutput2D[X[[10]],X[[11]],ContourStyle->Col],

SegOutput2D[X[[13]],X[[14]],ContourStyle->Col],
SegOutput2D[X[[14]],X[[15]],ContourStyle->Col],
SegOutput2D[X[[15]],X[[16]],ContourStyle->Col],
SegOutput2D[X[[16]],X[[13]],ContourStyle->Col],
SegOutput2D[X[[17]],X[[18]],ContourStyle->Col],
SegOutput2D[X[[19]],X[[20]],ContourStyle->Col]

} ];




Bazooka0={
(*1*)Pnt[{0,80}],
(*2*)Pnt[{20,60}],
(*3*)Pnt[{50,80}],
(*4*)Pnt[{0,40}],
(*5*)Pnt[{30,40}],
(*6*)Pnt[{30,10}],
(*7*)Pnt[{-15,10}],
(*8*)Pnt[{-30,10}],

(*9:C1*)Cir[{0,80},{20,100},{-20,100}],

(*10*)Pnt[{-20,100}],
(*11*)Pnt[{-30,100}],
(*12*)Pnt[{-30,80}],
(*13*)Pnt[{80,80}],
(*14*)Pnt[{80,100}],
(*15*)Pnt[{20,100}]
};
BazookaOutSet2D[X_,Range_,Col_]:=Module[{Out},
Out={
CGAOutput2D[X[[9]],Range,ContourStyle->Col] ,

SegOutput2D[X[[1]],X[[2]],ContourStyle->Col],
SegOutput2D[X[[2]],X[[3]],ContourStyle->Col],
SegOutput2D[X[[1]],X[[4]],ContourStyle->Col],
SegOutput2D[X[[4]],X[[5]],ContourStyle->Col],
SegOutput2D[X[[5]],X[[6]],ContourStyle->Col],
SegOutput2D[X[[4]],X[[7]],ContourStyle->Col],
SegOutput2D[X[[7]],X[[8]],ContourStyle->Col],

SegOutput2D[X[[10]],X[[11]],ContourStyle->Col],
SegOutput2D[X[[11]],X[[12]],ContourStyle->Col],
SegOutput2D[X[[12]],X[[13]],ContourStyle->Col],
SegOutput2D[X[[13]],X[[14]],ContourStyle->Col],
SegOutput2D[X[[14]],X[[15]],ContourStyle->Col]
} ];




RS=15;RM=35;RL=60;
RG=10;Gnum=12;Gs=7;
Wheel0=Join[{
(*1*)Pnt[{0,0}],
(*2:C1*)Cir[{RS,0},{-RS,0},{0,RS}],
(*3:C1-2*)Cir[{(RS+2),0},{-(RS+2),0},{0,(RS+2)}],
(*4:C2-1*)Cir[{RM,0},{-RM,0},{0,RM}],
(*5:C2-2*)Cir[{(RM+2),0},{-(RM+2),0},{0,(RM+2)}],
(*6:C3-1*)Cir[{RL,0},{-RL,0},{0,RL}],
(*7:C3-2*)Cir[{(RL+2),0},{-(RL+2),0},{0,(RL+2)}]
},Table[Rotor[Pnt[{(RL+2),0}],Biv[{1,0},{0,1}],2i \[Pi]/Gnum]
,{i,1,Gnum,1} ]
];



WheelOutSet2D[X_,Range_,Col_]:=Module[{Out,ColSet={Red,Pink,Orange,Yellow,LightGreen,Green
,Cyan,Blue,LightPurple,Purple,Magenta,Brown}},

Out=Show[
CGAOutput2D[X[[1]],Range,PlotStyle->Col] ,
SegOutput2D[X[[1]], Translator[X[[1]],Vec[{30,-100}]] ,ContourStyle->Gray],
SegOutput2D[X[[1]], Translator[X[[1]],Vec[{-30,-100}]] ,ContourStyle->Gray],
SegOutput2D[Translator[X[[1]],Vec[{30,-100}]], Translator[X[[1]],Vec[{-30,-100}]] ,ContourStyle->Gray],

CGAOutput2D[X[[2]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[3]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[4]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[5]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[6]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[7]],Range,ContourStyle->Black] ,


Table[{
SegOutput2D[X[[1]],X[[(Gs+i)]] ,ContourStyle->Gray ],

CGAOutput2D[OuterProduct[
X[[(Gs+i)]],
 Translator[X[[(Gs+i)]],Vec[{0,-2RG}]],
 Translator[X[[(Gs+i)]],Vec[{-RG,-RG}]]
],Range,ContourStyle->ColSet[[i]] ] ,

CGAOutput2D[X[[(Gs+i)]],Range,PlotStyle->Black] 
},{i,1,Gnum,1} ]

] ];





WheelOutSet2D1[X_,Range_]:=Module[{Out},

Out=Show[
CGAOutput2D[X[[1]],Range] ,
SegOutput2D[X[[1]], Translator[X[[1]],Vec[{30,-100}]] ,ContourStyle->Gray],
SegOutput2D[X[[1]], Translator[X[[1]],Vec[{-30,-100}]] ,ContourStyle->Gray],
SegOutput2D[Translator[X[[1]],Vec[{30,-100}]], Translator[X[[1]],Vec[{-30,-100}]] ,ContourStyle->Gray],

CGAOutput2D[X[[2]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[3]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[4]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[5]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[6]],Range,ContourStyle->Black] ,
CGAOutput2D[X[[7]],Range,ContourStyle->Black] 

] ];
WheelOutSet2D2[X_,Range_]:=Module[{Out,ColSet={Red,Pink,Orange,Yellow,LightGreen,Green
,Cyan,Blue,LightPurple,Purple,Magenta,Brown}},

Out=Show[
CGAOutput2D[X[[1]],Range] ,
Table[{
SegOutput2D[X[[1]],X[[(Gs+i)]] ,ContourStyle->Gray ],

CGAOutput2D[OuterProduct[
X[[(Gs+i)]],
 Translator[X[[(Gs+i)]],Vec[{0,-2RG}]],
 Translator[X[[(Gs+i)]],Vec[{-RG,-RG}]]
],Range,ContourStyle->ColSet[[i]] ] ,

CGAOutput2D[X[[(Gs+i)]],Range,PlotStyle->Black] 
},{i,1,Gnum,1} ]

] ];




EndPackage[];
