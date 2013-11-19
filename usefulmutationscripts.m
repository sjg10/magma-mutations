sylvrange:=20;
Syl:=[2];
for i in [1..sylvrange - 1] do
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

function mutate(wts,base,face)
    k:=#face;
    sum:=&+[Integers() | wts[i] : i in face];
    l0:=wts[base];
    bool,gcd:=IsDivisibleBy(l0^(k-1),sum^(k-2));
    if not bool then return false,_; end if;
    if not IsDivisibleBy(l0 * sum,gcd) then return 
false,_; end if;
    if not IsDivisibleBy(l0 * sum^2,gcd^2) then 
return false,_; end if;
    newwts:=[Integers() | l0 * wts[i] : i in face];
    Append(~newwts,sum^2);
    for i in [j : j in [1..#wts] | j ne base and 
not j in face] do
        Append(~newwts,sum * wts[i]);
    end for;
    redwts:=[Integers()|];
    for wt in newwts do
        bool,rwt:=IsDivisibleBy(wt,gcd);
        if not bool then return false,_; end if;
        Append(~redwts,rwt);
    end for;
    if GCD(redwts) ne 1 then return false,_; end 
if;
    Sort(~redwts);
    return true,redwts;
end function;

function onestep(wts)
    res:={PowerSequence(Integers()) | Sort(wts)};
    n:=#wts;
    for base in [1..n] do
        idxs:=Exclude({1..n},base);
        for k in [2..n - 1] do
            for face in Subsets(idxs,k) do
                bool,newwts:=mutate(wts,base,face);
                if bool then
                    Include(~res,newwts);
                end if;
            end for;
        end for;
    end for;
    return res;
end function; 

function is_canonical(wts)
    Sort(~wts);
    h:=&+wts;
    n:=#wts - 1;
    for k in [2..h - 2] do
        s:=&+[(wt * k) mod h : wt in wts];
        s:= s/h;
        if s lt 1 or s gt n-1 then
            return k;
        end if;
    end for;
    return true;
end function;

function breaks_canonical_on_k(wts,k)
    Sort(~wts);
    wts:=[Integers()!w : w in wts];
    h:=&+wts;
    n:=#wts - 1;
    s:=&+[(wt * k) mod h : wt in wts];
    s:= s/h;
    if s lt 1 or s gt n-1 then
        return true;
    end if;
    return false;
end function;


for n in [5..5] do
    S:=Syl[1..n-1];
    tt:=&*S;
    a:=3; //must be in 1 to n-1
    print n;
    X:=[[1,2*tt/S[a],1],[1,2*tt/S[a],(2*tt/S[a]+1)^2]];
    for i in [1..n-1] do
        if i ne a then
            Append(~X[1],2*tt/S[i]);
            Append(~X[2],(2*tt/S[i])*(2*tt/S[a]+1));
        end if;
    end for;
    for i in [3..50] do
        Append(~X,[X[i-1][3],X[i-1][2],((X[i-1][2]+X[i-1][3])^2)/X[i-1][1]]);
        for j in [1..n-1] do
            if j lt a then
                Append(~X[i],X[i-1][j+3]*(X[i-1][2]+X[i-1][3])/X[i-1][1]);
            elif j gt a then
                Append(~X[i],X[i-1][j+2]*(X[i-1][2]+X[i-1][3])/X[i-1][1]);
            end if;
        end for;
        //check on the new guy
        h:=&+X[i-1];
        for j in [2..2] do
            if j lt a then
                Floor(X[i][j]-X[i][j+3]/h)-(X[i][j+3]-X[i][j+3]/h);
            elif j gt a then
                Floor(X[i][j+2]-X[i][j+2]/h)-(X[i][j+2]-X[i][j+2]/h);
            end if;
        end for;
    end for;
end for;
print "MEOW";
