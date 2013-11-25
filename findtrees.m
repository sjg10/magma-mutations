//Study of mutation tree of conjectured maximal canonical,terminal WPS as per:
//[Kas13] Alexander Kasprzyk, Classifying terminal weighted projective space,arXiv:1304.3029 [math.AG], 2013.
//and
// [AKN13] Gennadiy Averkov, Jan Kumpelmann, and Benjamin Nill, Largest integral simplices with one interior integral point: Solution of Hensley's conjecture and related results, arXiv:1309.7967 [math.CO] , 2013.
load "usefulmutationsscripts.m";

//Finds the mutation tree of the conjectured maximal canonical WPS
function CanonicalWPSMutationTree(max_n,max_depth)
    Syl:=[2];
    for i in [1..max_n - 1] do
        Append(~Syl,1 + &*Syl);
    end for;

    function maximum_reflexive(n)
        S:=Syl[1..n-1];
        tt:=2 * &*S;
        wts:=[Integers() | tt / y : y in S];
        Append(~wts,1);
        Append(~wts,1);
        Sort(~wts);
        return wts;
    end function;

    for n in [4..max_n] do
        print mutation_tree(max_depth,maximum_reflexive(n));
    end for;
end function;


//Finds the mutation tree of the conjectured maximal terminal WPS
function TerminalWPSMutationTree(max_n,max_depth)
    Syl:=[2];
    for i in [1..max_n - 1] do
        Append(~Syl,1 + &*Syl);
    end for;

    function maximum_terminal(n)
        S:=Syl[1..n-1];
        tt:=&*S;
        wts:=[Integers() | tt / y : y in S];
        Append(~wts,1);
        Append(~wts,1);
        Sort(~wts);
        return wts;
    end function;

    for n in [max_n..max_n] do
        print mutation_tree(max_depth,maximum_terminal(n));
    end for;
    return true;
end function;
