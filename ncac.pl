% ncac.pl
% code for ncac.tex

:- (dynamic fineLog/1).

% run -- do all the checks.

run :-
    format('Settin up the logics~n~n'),
    loadLogics,
    format('~nMaking sure logic fine is actually the product of FDE and AC_2~n~n'),
    makeProduct(fde,ac2,fine16),
    isIso(I, fine,fine16),
    showHom(I, fine, fine16),
    format('~nShow all homomorphisms from FC to NC~n~n'),
    (showHoms ; true),
    format('~nCheck soundness of some 7-valued matrices~n~n'),
    (checkAx ; true),
    format('~nShow that the rest are also different from AC~n~n'),
    (checkAC ; true),
    format('~nFind and show all congruences of FC (this will take some time)~n~n'),
    (showCong(fine), fail ; true),
    format('~nDONE!~n'), !.

% loadLogics -- load all the logics discussed in ncac.tex

loadLogics :-
    loadLogic('ac2.lgc', ac2),
    loadLogic('fde.lgc', fde),
    loadLogic('nc.lgc', nc),
    loadLogic('fine16.lgc', fine),
    (   member(Vfde, [t,b]), 
        member(Vac, [f,n,t,b]), 
        makeFineProduct(Vfde, Vac), 
        fail;
        true
    ).

% showHoms -- show the homomorphisms from Fine's FC to Ferguson's NC.

showHoms :-
    isHom(Hom, fine, nc),
    showHom(Hom, fine, nc),
    fail.

% checkAx -- check the sixteen 7-valued matrices for soundness
% wrt to Ferguson's axioms.

checkAx :-
    member(Lg, [fine7bf,fine7bfs,fine7bn,fine7bns,fine7tb,fine7tbs,fine7tf,fine7tfs,fine7tn,fine7tns,fine7tt,fine7tts,fine7bb,fine7bbs,fine7bt,fine7bts]),
    checkAx(Lg),
    fail.

% checkAC -- four logics are sound wrt to all the axioms; show that
% they make some inferences valid that shouldn't be.

checkAC :-
    member(Lg, [fine7bb,fine7bbs,fine7bt,fine7bts]),
    checkSublogicAC(Lg),
    fail.

% checkIsos -- suceeds if Lg1 and Lg2 are FC_Vw^(*) 

checkIsos :-
    setof(L, fineLog(L), Ls),
    setof(P, A^B^(member(A, Ls), member(B, Ls), 
        sort([A,B], P), length(P,2)), Ps),
    member([Lg1, Lg2], Ps),
    (isIso(H,Lg1,Lg2)
    ->  showHom(H,Lg1,Lg2)
    ;   format('~w and ~w not isomorphic~n', [Lg1,Lg2])
    ),
    fail.

% checkHoms -- check if AC2 or FDE is a homomorphic image of a
% FC_Vw^(*)

checkHoms :-
    fineLog(Lg),
    (isHom(H,Lg,ac2)
    ->  format('Homomorphism from ~w to AC_2 found:~n', [Lg]),
        showHom(H,Lg,ac2)
    ;   format('No homomorphism from ~w to AC_2~n', [Lg])
    ),
    (isHom(H,Lg,fde)
    ->  format('Homomorphism from ~w to FDE found:~n', [Lg]),
        showHom(H,Lg,fde)
    ;   format('No homomorphism from ~w to FDE~n', [Lg])
    ), fail.

% axioms of AC

axiom(ac1a, A, neg(neg(A))).
axiom(ac1b, neg(neg(A)), A).
axiom(ac2, A, and(A, A)).
axiom(ac3, and(A,B), A).
axiom(ac5a, or(A,or(B,C)), or(or(A,B),C)).
axiom(ac5b, or(or(A,B),C), or(A,or(B,C))).
axiom(ac6a, or(A,and(B,C)), and(or(A,B),or(A,C))).
axiom(ac6b, and(or(A,B),or(A,C)), or(A,and(B,C))).

% axiom(e1, A, neg(neg(A))).
% axiom(e2, A, and(A, A)).
% axiom(e3, and(A, B), and(B, A)).
% axiom(e4, and(and(A, B), C), and(A, and(B, C))).
% axiom(e5, A, or(A,A)).
% axiom(e6, or(A, B), or(B, A)).
% axiom(e7, or(or(A, B), C), or(A, or(B, C))).
% axiom(e8, neg(and(A,B)), or(neg(A),neg(B))).
% axiom(e9, neg(or(A,B)), and(neg(A),neg(B))).
% axiom(e10, and(A,or(B,C)), or(and(A,B),and(A,C))).
% axiom(e11, or(and(A,B),and(A,C)), and(A,or(B,C))).

% checkAx(Lg) -- check all the axioms of AC if they are valid in Lg

checkAx(Lg) :- 
    logName(Lg, LN),
    format('Testing logic ~s~n', [LN]),
    (   forall(axiom(Ax, _, _),
            checkAx(Lg, Ax))
    ;   true
    ).

checkAx(Lg, Ax) :-
    format('  Checking axiom ~w in ~w~n', [Ax, Lg]),
    logTVs(Lg, TVs),
    logDTVs(Lg, DTVs),
    axiom(Ax, A, B),
    term_variables((A,B), Vars),
    (   (listOfTVs(Vars, TVs),
        hasValue(Lg, A, V1),
        member(V1, DTVs),
        hasValue(Lg, B, V2),
        \+ member(V2, DTVs), ! ) 
    ->
        format('  Axiom ~w fails in ~w:~n    ~w = ~w but~n    ~w = ~w~n',
            [Ax, Lg, A, V1, B, V2])
    ;   true 
    ).

% checkSublogicAC(Lg) -- checks if Lg is a sublogic of AC by looking for a
% consequence valid in Lg not valid in NC.

checkSublogicAC(Lg) :-
    findFmla(Lg, and(A,B)),
    isConseq(Lg, [A], B), 
    \+ isConseq(nc, [A], B),
    logName(Lg, LN),
    format('Logic ~w is not a sublogic of AC:~n', [LN]),
    prettyCopy(A, Ar),
    prettyCopy(B, Br),
    format('  ~w entails ~w~n', [Ar,Br]),
    format('  in ~w but not in AC~n', [LN]),
    !.

% checkACN -- check if inference rule ACN is validity preserving in Lg.

checkAC7(Lg) :-
    findFmla(Lg, and(A,B)),
    isConseq(Lg,[A],B),
    isConseq(Lg,[B],A),
    \+ isConseq(Lg,[neg(A)],neg(B)),
    prettyFmla([A,B]).
checkAC8(Lg) :-
    findFmla(Lg, and(A,and(B,C))),
    isConseq(Lg,[A],B),
    \+ isConseq(Lg,[or(A,C)],or(B,C)),
    prettyFmla([A,B,C]).
checkAC9(Lg) :-
    findFmla(Lg, and(A,and(B,C))),
    isConseq(Lg,[A],B),
    isConseq(Lg,[B],C),
    \+ isConseq(Lg,[A],C),
    prettyFmla([A,B,C]).

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
    format(atom(Lg), 'fine7~w~w', [Vfde,Vac]),
    deleteLogic(Lg),
    assertz(logTVs(Lg, TVs)),
    assertz(logDTVs(Lg, DTVs)),
    assertz(logNDTVs(Lg, NDTVs)),
    retractall(fineLog(Lg)),
    assertz(fineLog(Lg)),
    forall(logOp(fde, Op/Ar, Map1),
    (   logOp(ac2, Op/Ar, Map2),
        mapFineProduct(Vfde, Vac, Map1, Map2, Map),
        assertz(logOp(Lg, Op/Ar, Map)))),
    format(atom(LN), 'FC_~w~w', [Vfde,Vac]),
    assertz(logName(Lg, LN)),
    setColors(Lg, all),
    format('Logic ~w stored as ~w~n', [LN, Lg]),
    format(atom(Lg2), 'fine7~w~ws', [Vfde,Vac]),
    format(atom(LN2), 'FC_~w~w^*', [Vfde,Vac]),
    copyLogic(Lg, Lg2, LN2),
    retractall(fineLog(Lg2)),
    assertz(fineLog(Lg2)),
    subtract(DTVs1, [Vfde], Vfde2),
    (member(Vac, [t, b]) ->
        setProduct(Vfde2, [t, b], Vs),
        designateTVs(Lg2, Vs)
    ;   setProduct(Vfde2, [n, f], Vs),
        undesignateTVs(Lg2, Vs)
    ),
    setColors(Lg2, all),
    format('Logic ~w stored as ~w~n', [LN2, Lg2]).

% setFineProduct(Vfde, Vac, A1, A2, B) -- B is the set of truth values
% of FC_Vfde/Vac

setFineProduct(Vfde, Vac, A1, A2, B) :-
    setof((P1, P2),
    finePair(Vfde, Vac, P1, P2, A1, A2), B).

finePair(Vfde, Vac, Vfde, P2, _, A2) :-
    member(P2, A2).
finePair(Vfde, Vac, P1, Vac, A1, _) :-
    member(P1, A1).

% mapFineProduct(Vfde, Vac, M1, M2, B) -- B is the map resulting from applying maps
% M1 and M2 component-wise, but with Vac "dominant".

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
