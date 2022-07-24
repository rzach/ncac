% ncac.pl
% code for ncac.tex

:- (dynamic fineLog/1).

% run -- do all the checks.

run :-
    format('Settin up the logics~n~n'),
    loadLogics,
    format('~n~nMaking sure logic fine is actually the product of FDE and AC_2~n~n'),
    makeProduct(fde,ac2,fine16),
    isIso(I, fine,fine16),
    showHom(I, fine, fine16),
    format('~n~nShow all homomorphisms from FC to NC~n~n'),
    (showHoms ; true),
    format('~n~nFind and show all congruences of FC (this will take some time)~n~n'),
    (showCong(fine), fail ; true),
    fineSeven,
    format('~nDONE!~n'), 
    !.

% fineSeven -- run through the 7-valued matrices

fineSeven :-
    format('~n~nCheck soundness of some 7-valued matrices~n~n'),
    (checkAx ; true),
    format('~n~nShow that the rest are also different from AC~n~n'),
    (checkAC ; true).

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
% wrt to the Ferguson axioms.

checkAx :-
    fineLog(Lg),
    checkAx(Lg),
    fail.

% checkAC -- four logics are sound wrt to all the axioms; find some
% inferences they make valid that are invalid in NC

checkAC :-
    member(Lg, [fine7bb,fine7bbs,fine7bt,fine7bts]),
    checkSublogicAC(Lg),
    fail.

% checkIsos -- succeeds if Lg1 and Lg2 are FC_Vw^(*) 

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
axiom(ac3, and(A,_B), A).
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

% checkAx(Lg) -- check if all the axioms of AC are valid in Lg

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
        format('  Axiom ~w fails in ~w:~n    ~w = ~w is designated but~n    ~w = ~w is not~n',
            [Ax, Lg, A, V1, B, V2])
    ;   true 
    ).

% checkSublogicAC(Lg) -- checks if Lg is a sublogic of AC by
% looking for a consequence valid in Lg not valid in NC.

checkSublogicAC(Lg) :-
    findFmla(Lg, and(A,B)),
    isConseq(Lg, [A], B), 
    \+ isConseq(nc, [A], B),
    logName(Lg, LN),
    format('Logic ~w is not a sublogic of AC:~n', [LN]),
    prettyCopy((A,B), (Ar,Br)),
    format('  ~w entails ~w in ~w', [Ar,Br,LN]),
    format('  but not in AC:~n', []),
    logTVs(nc, TVs),
    logDTVs(nc, DTVs),
    term_variables((A,B), Vars),
    listOfTVs(Vars, TVs),
    hasValue(nc, A, V1),
    member(V1, DTVs),
    hasValue(nc, B, V2),
    \+ member(V2, DTVs), 
    format('  ~w = ~w is designated but~n    ~w = ~w is not~n',
            [A, V1, B, V2]),
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

% makeFineProduct(Vfde, Vac) -- defines the two 7-valued Fine matrices 
% for values Vfde and Vac, i.e., FC_Vfde/Vac and FC^*_Vfde/Vac

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
    showLogic(Lg),
    % now make the starred logic
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
    format('Logic ~w stored as ~w~n', [LN2, Lg2]),
    showLogic(Lg2).

% setFineProduct(Vfde, Vac, A1, A2, B) -- B is the set of truth values
% of FC_Vfde/Vac (A1 and and A2 are the truth values of FDE and AC2)

setFineProduct(Vfde, Vac, A1, A2, B) :-
    setof((P1, P2),
    finePair(Vfde, Vac, P1, P2, A1, A2), B).

% finePair(Vfde, _Vac, P1, P2, A1, A2) -- If A1 and A2 are the truth 
% values of FDE and AC, respectively, then (P1, P2) is a truth value of 
% FC_Vfde/Vac, i.e., either P1 = Vfde and P2 is any truth value of AC, or 
% P1 != Vfde, then P2 = Vac.

finePair(Vfde, _Vac, Vfde, P2, _, A2) :-
    member(P2, A2).
finePair(_Vfde, Vac, P1, Vac, A1, _) :-
    member(P1, A1).

% mapFineProduct(Vfde, Vac, M1, M2, B) -- B is the map resulting 
% from applying maps M1 and M2 component-wise, but with Vac "dominant".

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
