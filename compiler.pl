/*
   Julian Pszczolowski
   Algol 16 compiler
   *** SWIPL 7.X NEEDED ***
*/

/*
   LEXICAL ANALYSIS
*/ 

lexer(Tokens) -->
   white_space,
   (  (
         "+",       !, { Token = tokPlus }
      ;  "-",       !, { Token = tokMinus }
      ;  "*",       !, { Token = tokTimes }
      ;  "<>",      !, { Token = tokNeq }
      ;  "<=",      !, { Token = tokLeq }
      ;  "<",       !, { Token = tokLt }
      ;  ">=",      !, { Token = tokGeq }
      ;  ">",       !, { Token = tokGt }
      ;  "=",       !, { Token = tokEq }
      ;  ":=",      !, { Token = tokAssgn }
      ;  ";",       !, { Token = tokSColon }
      ;  ",",       !, { Token = tokComma }
      ;  "(",       !, { Token = tokLParen }
      ;  ")",       !, { Token = tokRParen }
      ;  digit(D),  !,
            number(D, N),
            { Token = tokNumber(N) }
      ;  letter(L), !, identifier(L, Id),
            {  member((Id, Token), [ (and, tokAnd),
                                     (begin, tokBegin),
                                     (div, tokDiv),
                                     (do, tokDo),
                                     (done, tokDone),
                                     (else, tokElse),
                                     (end, tokEnd),
                                     (fi, tokFi),
                                     (if, tokIf),
                                     (local, tokLocal),
                                     (mod, tokMod),
                                     (not, tokNot),
                                     (or, tokOr),
                                     (program, tokProgram),
                                     (read, tokRead),
                                     (then, tokThen),
                                     (value, tokValue),
                                     (while, tokWhile),
                                     (write, tokWrite) ]),
               !
            ;  Token = tokVar(Id)
            }
      ;  [_],
            { Token = tokUnknown }
      ),
      !,
         { Tokens = [Token | TokList] },
      lexer(TokList)
   ;  [],
         { Tokens = [] }
   ).

%anything remembers last character
anything(Last) -->
   [Char],
   {
      code_type(Char, ascii),
      [Last] = `*`,
      [Char] = `)`, !,
      fail
   }.

anything(_) -->
   [Char],
   { code_type(Char, ascii) }, 
   anything(Char).

anything(_) -->
      [].

white_space -->
   "(*",
   anything([]),
   "*)", !,
   white_space.

white_space -->
   [Char], { code_type(Char, space) }, !, white_space.

white_space -->
   [].

digit(D) -->
   [D],
      { code_type(D, digit) }.

digits([D|T]) -->
   digit(D),
   !,
   digits(T).

digits([]) -->
   [].

number(D, N) -->
   digits(Ds),
      { number_chars(N, [D|Ds]) }.

letter(L) -->
   [L], { code_type(L, alpha) }.

alphanum([A|T]) -->
   [A], { code_type(A, csym)
   ; [A] = `'` }, !,
   alphanum(T).
alphanum([]) -->
   [].

identifier(L, Id) -->
   alphanum(As),
      { atom_codes(Id, [L|As]) }.

/*
   FUNCTION USED IN PARSER
*/

%this function is creating adress for each variable in declaration list
make_global_adresses_declarations([], [], _) :- !.

make_global_adresses_declarations(DeclIn, DeclOut, Num) :-
   DeclIn = [variable(Id) | T],
   Num1 is Num - 1,
   make_global_adresses_declarations(T, T1, Num1),
   DeclOut = [variable(Id, Num) | T1].

/*
   SYNTAX ANALYSIS
   based on TWi's while_parser.pl
*/

%I don't want these
:- op(0, xfy, mod).
:- op(0, xfy, div).

program(Ast) -->
   [tokProgram],
   [tokVar(Id)],
   block(Block),
   { Ast = program(Id, Block) }.

block(Block) -->
   declarations(Declarations),
   {
      flatten(Declarations, Declarations1),  
      make_global_adresses_declarations(Declarations1, Declarations2, 65530),
      % 65530, 65529, ... are adresses for global variables 
      DecList = Declarations2
   },
   [tokBegin],
   %I give nearly every function below a list of declarations (DecList)
   %in order to link every variable occurence with an adress in memory
   complex_instruction(CInstr, DecList),
   [tokEnd],
   {
      Block = block(DecList, CInstr)
   }.
   
declarations(Declarations) -->
   declaration(Declaration), !,
   declarations(DeclarationsNext),
   { append([Declaration], DeclarationsNext, Declarations) }.
   
declarations([]) -->
   [].
   
declaration(Declaration) -->
   declarator(Declaration).

declarator(Declarator) -->
   [tokLocal],
   variables(Declarator).

variables(Vars) -->
   variable(Var),
   variables_next(VarsNext),
   { append([Var], VarsNext, Vars) }.

variables_next(VarsNext) -->
   [tokComma], !,
   variable(Var),
   variables_next(VarsNextNext),
   { append([Var], VarsNextNext, VarsNext) }.

variables_next([]) -->
   [].

variable(Var) -->
   [tokVar(Id)],
   { Var = variable(Id) }.

complex_instruction(CInstr, DecList) -->
   instruction(Instr, DecList),
   complex_instruction_next(CInstrNext, DecList),
   { append([Instr], CInstrNext, CInstr) }.

complex_instruction_next(CInstrNext, DecList) -->
   [tokSColon], !,
   instruction(Instr, DecList),
   complex_instruction_next(CInstrNextNext, DecList),
   { append([Instr], CInstrNextNext, CInstrNext) }.

complex_instruction_next([], _) -->
   [].

variable(Var, DecList) -->
   [tokVar(Id)],
   {
      member(variable(Id, Adress), DecList), !,
      Var = variable(Id, Adress)
   }.

instruction(Instr, DecList) -->
   (  [tokWhile], !, bool_expr(Bool, DecList), [tokDo], complex_instruction(CInstr, DecList), [tokDone],
         { Instr = while(Bool, CInstr) }
   ;  [tokIf], !, bool_expr(Bool, DecList), [tokThen], complex_instruction(ThenCInstr, DecList),
         (  [tokElse], !, complex_instruction(ElseCInstr, DecList), [tokFi],
               { Instr = if(Bool, ThenCInstr, ElseCInstr) }
         ;  [tokFi],
               { Instr = if(Bool, ThenCInstr) }
         )
   ;  variable(Var, DecList), !, [tokAssgn], arith_expr(Expr, DecList),
         { Instr = assign(Var, Expr) }
   ;  [tokRead], !, variable(Var, DecList),
         { Instr = read(Var) }
   ;  [tokWrite], arith_expr(Expr, DecList),
         { Instr = write(Expr) }
   ).

arith_expr(Expr, DecList) -->
   summand(Summand, DecList), arith_expr(Summand, Expr, DecList).

arith_expr(Acc, Expr, DecList) -->
   additive_op(Op), !, summand(Summand, DecList),
      { Acc1 =.. [Op, Acc, Summand] }, arith_expr(Acc1, Expr, DecList).

arith_expr(Acc, Acc, _) -->
   [].

summand(Expr, DecList) --> 
   factor(Factor, DecList), summand(Factor, Expr, DecList).

summand(Acc, Expr, DecList) -->
   multiplicative_op(Op), !, factor(Factor, DecList),
      { Acc1 =.. [Op, Acc, Factor] }, summand(Acc1, Expr, DecList).

summand(Acc, Acc, _) -->
   [].

factor(Factor, DecList) -->
   [tokMinus], !,
   simple_expr(SExpr, DecList),
   { Factor = minus(constant(0), SExpr) }.

factor(Factor, DecList) -->
   simple_expr(Factor, DecList).
   
simple_expr(SExpr, DecList) -->
   [tokLParen], !, arith_expr(SExpr, DecList), [tokRParen].

simple_expr(SExpr, DecList) -->
   atom_expr(SExpr, DecList).

atom_expr(AExpr, _) -->
   [tokNumber(Num)], !,
   { AExpr = constant(Num) }.

atom_expr(AExpr, DecList) -->
   variable(AExpr, DecList).

bool_expr(Bool, DecList) -->
   conjunction(Conjunction, DecList),
   bool_expr(Conjunction, Bool, DecList).

bool_expr(Acc, Bool, DecList) -->
   [tokOr], !, conjunction(Conjunction, DecList),
   { Acc1 =.. [or, Acc, Conjunction] },
   bool_expr(Acc1, Bool, DecList).

bool_expr(Acc, Acc, _) -->
   [].

conjunction(Conjunction, DecList) -->
   condition(Condition, DecList),
   conjunction(Condition, Conjunction, DecList).

conjunction(Acc, Conjunction, DecList) -->
   [tokAnd], !, condition(Condition, DecList),
   { Acc1 =.. [and, Acc, Condition] },
   conjunction(Acc1, Conjunction, DecList).

conjunction(Acc, Acc, _) -->
   [].
   
condition(Condition, DecList) -->
   [tokNot], !,
   rel_expr(RExpr, DecList),
   { Condition = not(RExpr) }.

condition(Condition, DecList) -->
   rel_expr(Condition, DecList).

rel_expr(RExpr, DecList) -->
   arith_expr(AExpr1, DecList),
   rel_op(Op), !,
   arith_expr(AExpr2, DecList),
   { RExpr =.. [Op, AExpr1, AExpr2] }.

rel_expr(RExpr, DecList) -->
   [tokLParen], bool_expr(RExpr, DecList), [tokRParen].

additive_op(plus) -->
   [tokPlus], !.
additive_op(minus) -->
   [tokMinus].

multiplicative_op(mult) -->
   [tokTimes], !.
multiplicative_op(div) -->
   [tokDiv], !.
multiplicative_op(mod) -->
   [tokMod].

rel_op(eq) -->
   [tokEq], !.
rel_op(neq) -->
   [tokNeq], !.
rel_op(lt) -->
   [tokLt], !.
rel_op(leq) -->
   [tokLeq], !.
rel_op(gt) -->
   [tokGt], !.
rel_op(geq) -->
   [tokGeq].

/*
   COMPILER
*/

code([], []).

code([H | T], Code) :-
   code(H, CodeH),
   code(T, CodeT),
   append(CodeH, CodeT, Code).

code(while(BExpr, CInstr), Code) :-
   code(BExpr, CodeBExpr),
   code(CInstr, CodeCInstr),
   Action = [const, 65535, swapa, load, swapa, load, swapd,
             const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             const, 65531, swapa, load, swapd, const, LabelAfterWhile, swapa, swapd, branchz],
   append([label(LabelCondition)], CodeBExpr, Code1),
   append(Code1, Action, Code2),
   append(Code2, CodeCInstr, Code3),
   append(Code3, [const, LabelCondition, jump], Code4),
   append(Code4, [label(LabelAfterWhile)], Code).

code(if(BExpr, CInstrThen), Code) :-
   code(BExpr, CodeBExpr),
   code(CInstrThen, CodeCInstrThen),
   Action = [const, 65535, swapa, load, swapa, load, swapd,
             const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             const, 65531, swapa, load, swapd, const, LabelAfterIf, swapa, swapd, branchz],
   append(CodeBExpr, Action, Code1),
   append(Code1, CodeCInstrThen, Code2),
   append(Code2, [label(LabelAfterIf)], Code).

code(if(BExpr, CInstrThen, CInstrElse), Code) :-
   code(BExpr, CodeBExpr),
   code(CInstrThen, CodeCInstrThen),
   code(CInstrElse, CodeCInstrElse),
   Action = [const, 65535, swapa, load, swapa, load, swapd,
             const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             const, 65531, swapa, load, swapd, const, LabelElse, swapa, swapd, branchz],
   append(CodeBExpr, Action, Code1),
   append(Code1, CodeCInstrThen, Code2),
   append(Code2, [const, LabelAfterElse, jump], Code3),
   append(Code3, [label(LabelElse)], Code4),
   append(Code4, CodeCInstrElse, Code5),
   append(Code5, [label(LabelAfterElse)], Code).

code(assign(Var, AExpr), Code) :-
   Var = variable(_, Adress),
   code(AExpr, CodeAExpr),
   CodeAssign = [const, 65535, swapa, load, swapa, load,
                 swapd, const, Adress, swapa, swapd, store,
                 const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store],
   append(CodeAExpr, CodeAssign, Code).

code(write(AExpr), Code) :-
   code(AExpr, CodeAExpr),
   CodeWrite = [const, 65535, swapa, load, swapa, load,
                swapd, const, 2, syscall,
                const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store],
   append(CodeAExpr, CodeWrite, Code).

code(read(variable(_, Adress)), Code) :-
   Code = [const, Adress, swapa, const, 1, syscall, store].

code(variable(_, Adress), Code) :-
   Code = [const, 1, swapd, const, 65535, swapa, load, sub, swapd, const,
           65535, swapa, swapd, store, swapd, const, Adress, swapa, load,
           swapd, swapa, swapd, store].

code(constant(Constant), Code) :-
   Code = [const, 1, swapd, const, 65535, swapa, load, sub, swapd, const,
           65535, swapa, swapd, store, swapd, const, Constant,
           swapd, swapa, swapd, store].

code(mod(AExpr1, AExpr2), Code) :-
   code(AExpr1, CodeAExpr1),
   code(AExpr2, CodeAExpr2),
   Action = [const, 65535, swapa, load, swapa, load, swapd,
             const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             swapa, load, swapd,
             const, 65531, swapa, load, div,
             const, -16, swapd, shift, swapd,
             const, 65535, swapa, load, swapa, swapd, store],
   append(CodeAExpr2, CodeAExpr1, CodeExprs),
   append(CodeExprs, Action, Code).

code(div(AExpr1, AExpr2), Code) :-
   code(AExpr1, CodeAExpr1),
   code(AExpr2, CodeAExpr2),
   Action = [const, 65535, swapa, load, swapa, load, swapd,
             const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             swapa, load, swapd,
             const, 65531, swapa, load, div, swapd,
             const, 65535, swapa, load, swapa, swapd, store],
   append(CodeAExpr2, CodeAExpr1, CodeExprs),
   append(CodeExprs, Action, Code).
   
code(mult(AExpr1, AExpr2), Code) :-
   code(AExpr1, CodeAExpr1),
   code(AExpr2, CodeAExpr2),
   Action = [const, 65535, swapa, load, swapa, load, swapd,
             const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             swapa, load, swapd,
             const, 65531, swapa, load, mul, swapd,
             const, 65535, swapa, load, swapa, swapd, store],
   append(CodeAExpr2, CodeAExpr1, CodeExprs),
   append(CodeExprs, Action, Code).

code(minus(AExpr1, AExpr2), Code) :-
   code(AExpr1, CodeAExpr1),
   code(AExpr2, CodeAExpr2),
   Action = [const, 65535, swapa, load, swapa, load,
             swapa, const, 1, swapd, const, 1, div, const, 1, swapd, swapa, shift, const, 65535, swapa, load, swapa, load,
             %line 468 is clearing upper 16 bits of acc and copying upper bit of the value of AExpr1
             %to the lowest bit of the upper part of acc
             %as it is needed for function code(lt(A, B), Code) to work properly
             swapd, const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             swapa, load, swapd,
             const, 65531, swapa, load, sub, swapd,
             const, 65535, swapa, load, swapa, swapd, store],
   append(CodeAExpr2, CodeAExpr1, CodeExprs),
   append(CodeExprs, Action, Code).

code(plus(AExpr1, AExpr2), Code) :-
   code(AExpr1, CodeAExpr1),
   code(AExpr2, CodeAExpr2),
   Action = [const, 65535, swapa, load, swapa, load, swapd,
             const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             swapa, load, swapd,
             const, 65531, swapa, load, add, swapd,
             const, 65535, swapa, load, swapa, swapd, store],
   append(CodeAExpr2, CodeAExpr1, CodeExprs),
   append(CodeExprs, Action, Code).

code(eq(AExpr1, AExpr2), Code) :-
   %I check whether AExpr1-AExpr2 is equal to 0
   code(minus(AExpr1, AExpr2), CodeMinus),
   Action = [const, 65535, swapa, load, swapa, load, swapd,
             const, LabelTrue, swapa, swapd, branchz],
   False = [const, 65535, swapa, load, swapa, const, 0, store],
   True = [const, 65535, swapa, load, swapa, const, 1, store],
   append(CodeMinus, Action, Code1),
   append(Code1, False, Code2),
   append(Code2, [const, LabelAfter, jump], Code3),
   append(Code3, [label(LabelTrue)], Code4),
   append(Code4, True, Code5),
   append(Code5, [label(LabelAfter)], Code).

code(lt(AExpr1, AExpr2), Code) :-
   %here I compute AExpr1-AExpr2, then shift the acc one position right,
   %and check whether or not acc is now negative
   % -- in fact this is checking the 17-th bit of AExpr1-AExpr2
   %the whole thing works because of line 468
   code(AExpr1, CodeAExpr1),
   code(minus(AExpr1, AExpr2), CodeMinus),
   ZeroUpper = [const, 1, swapd, const, 1, div],
   ShiftAOneAndPlusPC = [const, 65535, swapa, load, swapa, load, swapa, const, 1, swapd, swapa, shift,
                const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store],
   Check = [const, 65535, swapa, load, swapa, load, swapa, const, -1, swapd, swapa, shift, swapd,
            const, LabelTrue, swapa, swapd, branchn],
   True = [const, 65535, swapa, load, swapa, const, 1, store],
   False = [const, 65535, swapa, load, swapa, const, 0, store],
   append(ZeroUpper, CodeAExpr1, Code1),
   append(Code1, ShiftAOneAndPlusPC, Code2),
   append(Code2, CodeMinus, Code3),
   append(Code3, Check, Code4),
   append(Code4, False, Code5),
   append(Code5, [const, LabelAfter, jump], Code6),
   append(Code6, [label(LabelTrue)], Code7),
   append(Code7, True, Code8),
   append(Code8, [label(LabelAfter)], Code).

code(or(BExpr1, BExpr2), Code) :-
   %or is using nand, as or(a, b) iff nand(nand(a, a), nand(b, b))
   code(BExpr1, CodeBExpr1),
   code(BExpr2, CodeBExpr2),
   Action = [const, 65535, swapa, load, swapa, load, swapd, load, nand, swapd,
             const, 65531, swapa, swapd, store,
             const, 1, swapd, const, 65535, swapa, load, add, swapd, const, 65535, swapa, swapd, store,
             swapa, load, swapd, load, nand, swapd,
             const, 65531, swapa, load, nand, swapd,
             const, 65535, swapa, load, swapa, swapd, store],
   append(CodeBExpr1, CodeBExpr2, CodeExprs),
   append(CodeExprs, Action, Code).

%lines 544-560 weren't that hard
code(and(BExpr1, BExpr2), Code) :-
   code(eq(mult(BExpr1, BExpr2), constant(1)), Code).

code(not(BExpr), Code) :-
   code(minus(constant(1), BExpr), Code).

code(neq(AExpr1, AExpr2), Code) :-
   code(not(eq(AExpr1, AExpr2)), Code).

code(leq(AExpr1, AExpr2), Code) :-
   code(or(eq(AExpr1, AExpr2), lt(AExpr1, AExpr2)), Code).

code(gt(AExpr1, AExpr2), Code) :-
   code(not(leq(AExpr1, AExpr2)), Code).

code(geq(AExpr1, AExpr2), Code) :-
   code(not(lt(AExpr1, AExpr2)), Code).

%removes negative numbers from the list
%using property -X = 65536-X
remove_negative([], []).

remove_negative([H | T], Result) :-
   number(H), H < 0, !,
   H1 is H + 65536,
   remove_negative(T, Result1),
   append([H1], Result1, Result).

remove_negative([H | T], Result) :-
   remove_negative(T, Result1),
   append([H], Result1, Result).

fill([], [nop, nop, nop, nop]) :- !.
fill([A], [A, nop, nop, nop]) :- !.
fill([A, B], [A, B, nop, nop]) :- !.
fill([A, B, C], [A, B, C, nop]) :- !.
fill([A, B, C, D], [A, B, C, D]).

fill([], [nop, nop, nop, nop, X], X) :- !.
fill([A], [A, nop, nop, nop, X], X) :- !.
fill([A, B], [A, B, nop, nop, X], X) :- !.
fill([A, B, C], [A, B, C, nop, X], X) :- !.
fill([A, B, C, D], [A, B, C, D, X], X).

%groups instruction into fours by filling necessary space with nop's
group([], Result, Acc) :-
   fill(Acc, Result).

group([H | T], Result, Acc) :-
   \+ var(H), H = label(X), !,
   fill(Acc, Acc1, label(X)),
   group(T, Result1, []),
   append(Acc1, Result1, Result).

group([H | T], Result, Acc) :-
   (number(H) ; var(H)), !,
   fill(Acc, Acc1, H),
   group(T, Result1, []),
   append(Acc1, Result1, Result).

group([H | T], Result, Acc) :-
   length(Acc, Len),
   Len is 4, !,
   group([H | T], Result1, []),
   append(Acc, Result1, Result).

group([H | T], Result, Acc) :-
   append(Acc, [H], Acc1),
   group(T, Result, Acc1).

%counts line numbers and instantiates variable X with current line number
%whenever reaches label(X) 
create_labels([], [], _).

create_labels([H | T], Result, Num) :-
   (number(H) ; var(H)), !,
   Num1 is Num + 4,
   create_labels(T, Result1, Num1),
   append([H], Result1, Result).

create_labels([H | T], Result, Num) :-
   \+ var(H), H = label(X), !,
   X is div(Num, 4),
   create_labels(T, Result, Num).

create_labels([H | T], Result, Num) :-
   Num1 is Num + 1,
   create_labels(T, Result1, Num1),
   append([H], Result1, Result).

instr_conversion(nop, 0) :- !.
instr_conversion(syscall, 1) :- !.
instr_conversion(load, 2) :- !.
instr_conversion(store, 3) :- !.
instr_conversion(swapa, 4) :- !.
instr_conversion(swapd, 5) :- !.
instr_conversion(branchz, 6) :- !.
instr_conversion(branchn, 7) :- !.
instr_conversion(jump, 8) :- !.
instr_conversion(const, 9) :- !.
instr_conversion(add, 10) :- !.
instr_conversion(sub, 11) :- !.
instr_conversion(mul, 12) :- !.
instr_conversion(div, 13) :- !.
instr_conversion(shift, 14) :- !.
instr_conversion(nand, 15).

%e.g. converts [swapd, swapa, shift, swapd] into decimal form of 54e5
acc_conversion([A, B, C, D], Number) :-
   instr_conversion(A, ANum),
   instr_conversion(B, BNum),
   instr_conversion(C, CNum),
   instr_conversion(D, DNum),
   Num0 is 0,
   Num1 is Num0 * 16 + ANum,
   Num2 is Num1 * 16 + BNum,
   Num3 is Num2 * 16 + CNum,
   Num4 is Num3 * 16 + DNum,
   Number is Num4.

%function that takes every four instructions (or one number)
%and converts it into "SextiumBin" form
% -- numbers stay as they are
% -- four instructions are converted by acc_conversion function
convert_to_sextium([], [Result], Acc) :-
   acc_conversion(Acc, Result), !.

convert_to_sextium([H | T], Result, Acc) :-
   length(Acc, Len),
   Len is 4, !,
   acc_conversion(Acc, Number),
   convert_to_sextium([H | T], Result1, []),
   append([Number], Result1, Result).

convert_to_sextium([H | T], Result, []) :-
   number(H), !,
   convert_to_sextium(T, Result1, []),
   append([H], Result1, Result).

convert_to_sextium([H | T], Result, Acc) :-
   append(Acc, [H], Acc1),
   convert_to_sextium(T, Result, Acc1).

algol16(Source, SextiumBin) :-
   phrase(lexer(Tokens), Source),
   phrase(program(Ast), Tokens),
   Ast = program(_, block(Declarations, CInstr)),
   %DecLen is the length of global variables memory
   length(Declarations, DecLen),
   %65531, 65532, 65533, 65534 <- these memory cells are additional registers
   %but I really use only 65531
   SP is 65530 - DecLen,
   %I set stack pointer below global variables
   code(CInstr, Program1),
   append([const, 65535, swapa, const, SP, store], Program1, Program2),
   %stack pointer adress is at 65535 (ffff)
   append(Program2, [const, 0, syscall], Program3),
   remove_negative(Program3, Program4),
   group(Program4, Program5, []),
   create_labels(Program5, Program6, 0),
   convert_to_sextium(Program6, SextiumBin, []).
