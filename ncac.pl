% ncac.pl
% code for ncac.tex

:- (dynamic fineLog/1).

loadLogics :-
    loadLogic('ac2.lgc', ac2),
    loadLogic('fde.lgc', fde),
    loadLogic('nc.lgc', nc),
    loadLogic('fine16.lgc', fine),
    loadLogic('fine7Tf.lgc', fine7Tf),
    loadLogic('fine7Tn.lgc', fine7Tn),
    loadLogic('fine7Bf.lgc', fine7Bf),
    loadLogic('fine7Bn.lgc', fine7Bn).

showHoms :-
    isHom(Hom, fine, nc),
    showHom(Hom, fine, nc),
    fail.

axiom(A, neg(neg(A))).
axiom(A, and(A, A)).
axiom(and(A,B), and(B,A)).
axiom(and(A,and(B,C)), and(and(A,B),C)).
axiom(A, or(A,A)).
axiom(or(A,or(B,C)), or(or(A,B),C)).
axiom(neg(and(A,B)), or(neg(A),neg(B))).
axiom(neg(or(A,B)), and(neg(A),neg(B))).
axiom(and(A,or(B,C)), or(and(A,B),and(A,C))).
axiom(or(A,and(B,C)), and(or(A,B),or(A,C))).

showAxFails(Lg, A, B) :- 
    format('Testing logic ~w~n', Lg),
    logTVs(Lg, TVs),
    logDTVs(Lg, DTVs),
    ( axiom(A, B); axiom(B,A)),
    term_variables((A,B), Vars),
    listOfTVs(Vars, TVs),
    hasValue(Lg, A, V1),
    member(V1, DTVs),
    hasValue(Lg, B, V2),
    \+ member(V2, DTVs),
    format('~w = ~w but ~w = ~w, so entailment fails', [A, V1, B, V2]), !.

findIsoPairs(Lg1, Lg2) :-
    fineLog(Lg1),
    fineLog(Lg2),
    isIso(_,Lg1,Lg2).

% makeProduct(Lg1, Lg2, Lg12) -- defines a new logic Lg12 as the
% direct product of logics Lg1 and Lg2

makeFineProduct(Vfde, Vac) :-
    logTVs(fde, TVs1),
    logTVs(ac2, TVs2),
    setFineProduct(Vfde, Vac, TVs1, TVs2, TVs),
    logDTVs(fde, DTVs1),
    logDTVs(ac2, DTVs2),
    setProduct(DTVs1, DTVs2, DTV1s),
    intersection(DTV1s, TVs, DTVs),
    subtract(TVs, DTVs, NDTVs),
    format(atom(Lg12), 'fine7~w~w', [Vfde,Vac]),
    deleteLogic(Lg12),
    assertz(logTVs(Lg12, TVs)),
    assertz(logDTVs(Lg12, DTVs)),
    assertz(logNDTVs(Lg12, NDTVs)),
retractall(fineLog(Lg12)),
    assertz(fineLog(Lg12)),
    forall(logOp(fde, Op/Ar, Map1),
    (   logOp(ac2, Op/Ar, Map2),
        mapFineProduct(Vfde, Vac, Map1, Map2, Map),
        assertz(logOp(Lg12, Op/Ar, Map)))),
    format(atom(LN), 'FDE x AC_~w ~w', [Vfde,Vac]),
    assertz(logName(Lg12, LN)),
    setColors(Lg12, all).

% setProduct(A1, A2, B) -- B is the Cartesian product of sets A1 and A2

setFineProduct(Vfde, Vac, A1, A2, B) :-
    setof((P1, P2), finePair(Vfde, Vac, P1, P2, A1, A2), B).

finePair(Vfde, Vac, Vfde, P2, _, A2) :-
    member(P2, A2).
finePair(Vfde, Vac, P1, Vac, A1, _) :-
    member(P1, A1).


% mapProduct(M1, M2, B) -- B is the map resulting from applying maps
% M1 and M2 component-wise

mapFineProduct(Vfde, Vac, M1, M2, B) :-
    setof(Args:V,
        prodFineMap(Vfde, Vac, M1, M2, Args, V),
        B).

prodFineMap(Vfde, Vac, M1, M2, Args, (V1, V2)) :-
    member(A1:V1, M1),
    (
        V1 = Vfde
    ->
        member(A2:V2, M2)
    ;   member(A2:_, M2), V2 = Vac
    ),
    pairUp(A1, A2, Args).