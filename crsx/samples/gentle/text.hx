// HACS sample using text.

module "org.crsx.samples.gentle.FirstText" {


// LEXICAL ANALYSIS.

space [ \t\n] ;                                 // white space convention

token INT   | [0-9]+ ;
token SYM   | [A-Za-z]+ ([_] [0-9]+)* ;

sort Symbol | symbol ⟦⟨SYM⟩⟧ ;

sort List | ⟦⟨INT⟩ ⟨List⟩⟧ | ⟦⟨Symbol⟩ ⟨List⟩⟧ | ⟦⟧ ;

text | Echo(List);

Echo(⟦ ⟨INT#i⟩ ⟨List#rest⟩ ⟧) → text ⟦ ⟨#i⟩ ⟨ Echo(#rest) ⟩ ⟧;
Echo(⟦ ⟨Symbol#s⟩ ⟨List#rest⟩ ⟧) → text ⟦ ⟨#s⟩ ⟨ Echo(#rest) ⟩ ⟧;
Echo(⟦⟧) → text ⟦⟧ ;

}
