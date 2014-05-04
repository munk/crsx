module "net.sf.crsx.samples.gentle.Test" {
space [ \t\n] ;

token IDENTIFIER | [a-z] [A-Za-z_0-9]* ;

sort Id    | symbol ⟦⟨IDENTIFIER⟩⟧ ;

sort Stat  | ⟦ ⟨[xyzzy:Id]⟩ in ⟨Stat[xyzzy:Stat]⟩ ¶ ⟧ | ⟦ ⟧
           | sugar ⟦ { ⟨Stat#⟩ } ⟧ → Stat# ;

attribute  ↑ds(Defs) ;
sort Defs  | ⟦ def ⟨Defs⟩ ⟧ | ⟦ ⟧ ;

sort Defs  | scheme Get(Stat) ;
Get(#s) ↑ds(#ds) → #ds ;

sort Stat  | ↑ds ;
⟦ zzz in ⟨Stat #s[zzz] ↑ds(#ds)⟩ ⟧ ↑ds(⟦ def ⟨Defs#ds⟩ ⟧) ;
⟦⟧ ↑ds(⟦⟧) ;

}
