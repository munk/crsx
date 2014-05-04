module "net.sf.crsx.samples.gentle.Simple" {

// GOAL.

sort IAssign   | scheme Compile(Eqs) ;
Compile(#eqs) → ⟦ Generate TA ⟨Eqs#eqs⟩ ⟧ ;


// LEXICAL.

space [ \t\n] ;

token Num  | ⟨Digit⟩+ ("." ⟨Digit⟩+)? ("e" ⟨Digit⟩+)? ;
token Id   | [a-z] ⟨AlNum⟩+ ;

token fragment Digit  | [0-9] ;
token fragment AlNum  | [A-Za-z0-9_] ;


// SYNTAX.

sort Eqs   | ⟦ ⟨[x:Name]⟩ = ⟨Exp⟩ ; ⟨Eqs[x:Exp]⟩ ⟧
           | ⟦ ⟧
           ;

sort Name  | symbol ⟦⟨Id⟩⟧ ;

sort Exp   | ⟦ val ⟨[x:Name]⟩ ↦ ⟨Exp[x:Exp]⟩ ⟧
           | ⟦ seq ⟨[x:Name]⟩ ↦ ⟨Exp[x:Exp]⟩ ⟧
           | ⟦ ⟨Exp@1⟩ + ⟨Exp@2⟩ ⟧@1  |  ⟦ ⟨Exp@1⟩ - ⟨Exp@2⟩ ⟧@1
           | ⟦ ⟨Exp@2⟩ * ⟨Exp@3⟩ ⟧@2  |  ⟦ ⟨Exp@2⟩ / ⟨Exp@3⟩ ⟧@2
           | ⟦ ⟨Name⟩ ( ⟨Args⟩ ) ⟧@3
           | ⟦ ⟨Name⟩ ⟧@3
           | ⟦ ⟨Num⟩ ⟧@3
           | sugar ⟦ ( ⟨Exp#⟩ ) ⟧@3 → Exp#
           ;

sort Args      | ⟦ ⟨Exp⟩ ⟨ArgsTail⟩ ⟧ | ⟦⟧ ;
sort ArgsTail  | ⟦ , ⟨Exp⟩ ⟨ArgsTail⟩ ⟧ | ⟦⟧ ;


// TYPE ANALYSIS.

sort Type  | Unit | Sequence | Fun(Type,Type) ;

| scheme Unif(Type,Type) ;
Unif(Unit, Unit) → Unit;
Unif(Sequence, Unit) → Sequence;
Unif(Unit, Sequence) → Sequence;
Unif(Sequence, Sequence) → Sequence;

Unif(Fun(#t11,#t12), Fun(#t21, #t22))
 → Fun(Unif(#t11,#t21), Unif(#t12,#t22)) ;

default Unif(#1, #2) → error⟦Bad type⟧ ;

| scheme TailType(Type) ;
TailType(Fun(#t1, #t2)) → TailType(#t2) ;
default TailType(#t) → #t ;

attribute ↑t(Type);

sort Exp | ↑t;

⟦ val x ↦ ⟨Exp#e[x] ↑t(#t)⟩ ⟧ ↑t(Fun(Unit,#t)) ;
⟦ seq x ↦ ⟨Exp#e[x] ↑t(#t)⟩ ⟧ ↑t(Fun(Sequence,#t)) ;

⟦ (⟨Exp#1 ↑t(#t1)⟩ + ⟨Exp#2 ↑t(#t2)⟩) ⟧ ↑t(Unif(#t1,#t2));
⟦ (⟨Exp#1 ↑t(#t1)⟩ - ⟨Exp#2 ↑t(#t2)⟩) ⟧ ↑t(Unif(#t1,#t2));
⟦ (⟨Exp#1 ↑t(#t1)⟩ * ⟨Exp#2 ↑t(#t2)⟩) ⟧ ↑t(Unif(#t1,#t2));
⟦ (⟨Exp#1 ↑t(#t1)⟩ / ⟨Exp#2 ↑t(#t2)⟩) ⟧ ↑t(Unif(#t1,#t2));

⟦ ⟨Num#⟩ ⟧ ↑t(Unit);

attribute ↓e{Name:Type};

sort Exp | scheme ⟦ TA ⟨Exp⟩ ⟧ ↓e ;

⟦ TA x ⟧ ↓e{⟦x⟧ : #t} → ⟦ x ⟧ ↑t(#t);
⟦ TA x ⟧ ↓e{¬⟦x⟧} → error⟦Undefined identifier ⟨x⟩⟧ ;

⟦ TA f ( ⟨Args#as⟩ ) ⟧ ↓e{⟦f⟧:#t}
  → ⟦ f ( ⟨Args TA_Args(#as, #t)⟩ ) ⟧ ↑t(TailType(#t)) ;
⟦ TA f ( ⟨Args#as⟩ ) ⟧ ↓e{¬⟦f⟧} → error⟦Undefined function ⟨f⟩⟧ ;

⟦ TA val x ↦ ⟨Exp#e[x]⟩ ⟧ → ⟦ val x ↦ ⟨Exp ⟦TA ⟨Exp #e[x]⟩ ⟧ ↓e{⟦x⟧:Unit}⟩ ⟧ ;
⟦ TA seq x ↦ ⟨Exp#e[x]⟩ ⟧ → ⟦ seq x ↦ ⟨Exp ⟦TA ⟨Exp #e[x]⟩ ⟧ ↓e{⟦x⟧:Sequence}⟩ ⟧ ;
⟦ TA ⟨Exp#1⟩ + ⟨Exp#2⟩ ⟧ → ⟦ (TA ⟨Exp#1⟩) + (TA ⟨Exp#2⟩) ⟧ ;
⟦ TA ⟨Exp#1⟩ - ⟨Exp#2⟩ ⟧ → ⟦ (TA ⟨Exp#1⟩) - (TA ⟨Exp#2⟩) ⟧ ;
⟦ TA ⟨Exp#1⟩ * ⟨Exp#2⟩ ⟧ → ⟦ (TA ⟨Exp#1⟩) * (TA ⟨Exp#2⟩) ⟧ ;
⟦ TA ⟨Exp#1⟩ / ⟨Exp#2⟩ ⟧ → ⟦ (TA ⟨Exp#1⟩) / (TA ⟨Exp#2⟩) ⟧ ;
⟦ TA ⟨Num#n⟩ ⟧ → ⟦ ⟨Num#n⟩ ⟧ ;

sort Args | scheme TA_Args(Args,Type) ↓e ;

TA_Args(⟦ ⟨Exp#e ↑#t1⟩ ⟨ArgsTail#as⟩ ⟧, Fun(#t1, #t2))
  → ⟦ ⟨Exp#e ↑#t1⟩ ⟨ArgsTail TA_ArgsTail(#as, #t2)⟩ ⟧ ;
default TA_Args(#as, #t) → error⟦Bad argument type⟧ ;

sort ArgsTail | scheme TA_ArgsTail(ArgsTail,Type) ↓e ;

TA_ArgsTail(⟦ , ⟨Exp#e ↑#t1⟩ ⟨ArgsTail#as⟩ ⟧, Fun(#t1, #t2))
  → ⟦ , ⟨Exp#e ↑#t1⟩ ⟨ArgsTail TA_ArgsTail(#as, #t2)⟩ ⟧ ;
TA_ArgsTail(⟦ ⟧, #t1) → ⟦ ⟧ ;
default TA_ArgsTail(#as, #t) → error⟦Bad argument type⟧ ;

sort Eqs | scheme ⟦ TA ⟨Eqs⟩ ⟧ ↓e ;
⟦ TA x = ⟨Exp#e ↑t(#t)⟩; ⟨Eqs#eqs[x]⟩ ⟧ → ⟦ x = ⟨Exp#e⟩; ⟨Eqs ⟦TA ⟨Eqs#eqs[x]⟩⟧ ↓e{⟦x⟧:#t}⟩ ⟧ ;
⟦ TA ⟧ → ⟦ ⟧ ;


// LAMBDA LIFTING.

sort Eqs  | scheme ⟦ Lift ⟨Eqs⟩ ⟧ | scheme ⟦ PostLift ⟨Eqs⟩ ⟧ ;

⟦ Lift ⟧ → ⟦ ⟧ ;
⟦ Lift x = ⟨Exp#ex[x]⟩; ⟨Eqs#eqs[x]⟩ ⟧ → ⟦ PostLift x = Lift () ⟨Exp#ex[x]⟩ Outer; ⟨Eqs#eqs[x]⟩ ⟧ ;

⟦ PostLift x = ⟨Exp#ex[x]⟩ WHERE { }; ⟨Eqs#eqs2[x]⟩ ⟧
  → ⟦ x = ⟨Exp#ex[x]⟩; ⟨Eqs#eqs2[x]⟩ ⟧ ;
⟦ PostLift x = ⟨Exp#ex[x]⟩ WHERE { y = ⟨Exp#ey[x,y]⟩; ⟨Eqs#eqs1[x,y]⟩ }; ⟨Eqs#eqs2[x]⟩ ⟧
  → ⟦ x = ⟨Exp#ex[x]⟩; y = ⟨Exp#ey[x,y]⟩ WHERE { ⟨Eqs#eqs1[x,y]⟩ }; ⟨Eqs#eqs2[x]⟩ ⟧ ;

sort Exp  | scheme ⟦ Lift (⟨Args⟩) ⟨Exp⟩ ⟨InnerOuter⟩ ⟧ | scheme ⟦ Lift2 (⟨Args⟩) ⟨Exp⟩ ⟧
          | ⟦ ⟨Exp⟩ WHERE { ⟨Eqs⟩ } ⟧ ;

sort InnerOuter  | ⟦Inner⟧ | ⟦Outer⟧ ;

⟦ Lift (⟨Args#as⟩) val x ↦ ⟨Exp#e[x]⟩ Outer ⟧
  → ⟦ val x ↦ Lift (⟨Args ArgsAppendVal(#as,x)⟩ ⟨Exp#e[x]⟩ Outer ⟧ ;
⟦ Lift (⟨Args#as⟩) seq x ↦ ⟨Exp#e[x]⟩ Outer ⟧
  → ⟦ seq x ↦ Lift (⟨Args ArgsAppendSeq(#as,x)⟩ ⟨Exp#e[x]⟩ Outer ⟧ ;

⟦ Lift (⟨Args#as⟩) val x ↦ ⟨Exp#e[x]⟩ Inner ⟧
  → ⟦ n (⟨Args#as⟩) WHERE { n = val x ↦ ⟨Exp#e[x]⟩ } ⟧
⟦ Lift (⟨Args#as⟩) seq x ↦ ⟨Exp#e[x]⟩ Inner ⟧
  → ⟦ n (⟨Args#as⟩) WHERE { n = seq x ↦ ⟨Exp#e[x]⟩ } ⟧

⟦ Lift (⟨Args#as⟩) ⟨Exp#1⟩ + ⟨Exp#2⟩ ⟨InnerOuter#io⟩ ⟧
  → ⟦ 

⟦ Lift (⟨Args#as⟩) f ( ⟨Args#as↑l(#eqs)⟩ ) ⟧

⟦ Lift (⟨Args#as⟩) x ⟧

⟦ Lift (⟨Args#as⟩) ⟨Num#n⟩ ⟧




// OUTPUT CODE.

sort IBlock	| ⟦ { ⟨IAssign*⟩ } ⟧ ;

sort IAssign    | ⟦ ⟨IType⟩ ⟨Id⟩ = ⟨Id⟩ ⟨Id*⟩; ¶⟧
     		| ⟦ ⟨IType⟩ ⟨Id⟩ = ⟨IUnOp⟩ ⟨Id⟩; ¶⟧
		| ⟦ ⟨IType⟩ ⟨Id⟩ = ⟨Id⟩ ⟨IBinOp⟩ ⟨Id⟩; ¶⟧
		| ⟦ ⟨IType⟩ ⟨Id⟩ ( ⟨IArgs⟩ ) = { ⟨IAssign*⟩ return ⟨Id⟩; } ¶⟧
		| ⟦ ⟨IBlock⟩ ⟧
		;

sort IArgs	| ⟦ ⟨IType⟩ ⟨Id⟩ , ⟨IArgs⟩ ⟧ | ⟦ ⟨IType⟩ ⟨Id⟩ ⟧ ;

sort IUnOp	| ⟦LIFT⟧ | ⟦+⟧ | ⟦-⟧ ;
sort IBinOp	| ⟦ON⟧ | ⟦+⟧ | ⟦-⟧ | ⟦*⟧ | ⟦/⟧ ;

sort IType	| ⟦ SEQ ⟧ | ⟦ VAL ⟧ ;


sort IBlock;

| scheme ⟦ G_Eqs ⟨Eqs⟩ ⟧ ;
⟦ G_Eqs x = ⟨Exp#e⟩ ; ⟨Eqs#eqs[x]⟩ ⟧ → ⟦ { G_Exp x = ⟨Exp#e⟩ G_Eqs ⟨Eqs#eqs[x]⟩ } ⟧ ;
⟦ G_Eqs ⟧ → ⟦⟧ ;

| scheme ⟦ G_Exp ⟨Name⟩ = ⟨Exp⟩ ⟧ ;

⟦ G_Exp x = val y ↦ ⟨Exp#e[y]⟩ ⟧ → G_Exp_Fun(VAL, ⟦ val y ↦ 
⟦ G_Exp x = seq y ↦ ⟨Exp#e[y]⟩ ⟧ ↑n(#n) ↓vs(#vs) → ⟦ SEQ x = ⟨Id#n⟩ ⟨Id* #vs⟩; ⟧ ;

⟦ G_Exp ⟨Exp#1⟩ + ⟨Exp#2⟩ ⟧ ↓t(#t)
  → ⟦ {G_Exp n1 = ⟨Exp#1⟩} {G_Exp n2 = ⟨Exp#2⟩} ⟨IType T(#t)⟩ n = n1+n2; ⟧ ;
⟦ G_Exp ⟨Exp#1⟩ - ⟨Exp#2⟩ ⟧ ↓t(#t)
  → ⟦ {G_Exp n1 = ⟨Exp#1⟩} {G_Exp n2 = ⟨Exp#2⟩} ⟨IType T(#t)⟩ n = n1-n2; ⟧ ;
⟦ G_Exp ⟨Exp#1⟩ * ⟨Exp#2⟩ ⟧ ↓t(#t)
  → ⟦ {G_Exp n1 = ⟨Exp#1⟩} {G_Exp n2 = ⟨Exp#2⟩} ⟨IType T(#t)⟩ n = n1*n2; ⟧ ;
⟦ G_Exp ⟨Exp#1⟩ / ⟨Exp#2⟩ ⟧ ↓t(#t)
  → ⟦ {G_Exp n1 = ⟨Exp#1⟩} {G_Exp n2 = ⟨Exp#2⟩} ⟨IType T(#t)⟩ n = n1/n2; ⟧ ;

⟦ G_Exp ⟨Name⟩ ( ⟨Args⟩ ) ⟧
⟦ G_Exp ⟨Name⟩ ⟧
⟦ G_Exp ⟨Num⟩ ⟧

}
