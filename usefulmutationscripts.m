//Useful functions for working with mutations of WPS as per 
//[Kas13] Alexander Kasprzyk, Classifying terminal weighted projective space,arXiv:1304.3029 [math.AG], 2013.
//In particular with maximal reflexive/canonical WPS as per
//[Kas10] Alexander Kasprzyk, Canonical toric Fano threefolds, Canadian Journal of Mathematics 62(2010), 1293-1309

//Constructs the Sylvester sequence up to sylvrange on load
sylvrange:=20;
Syl:=[2];
for i in [1..sylvrange - 1] do
    Append(~Syl,1 + &*Syl);
end for;

//Return the weights of the maximal reflexive polytope of degree n
function maximum_reflexive(n)
    S:=Syl[1..n-1];
    tt:=2 * &*S;
    wts:=[Integers() | tt / y : y in S];
    Append(~wts,1);
    Append(~wts,1);
    Sort(~wts);
    return wts;
end function;

//mutates a weighted projective space over the specified base up to the specified face
function mutate(wts,base,face)
    k:=#face;
    sum:=&+[Integers() | wts[i] : i in face];
    l0:=wts[base];
    bool,gcd:=IsDivisibleBy(l0^(k-1),sum^(k-2));
    if not bool then return false,_; end if;
    if not IsDivisibleBy(l0 * sum,gcd) then 
		return false,_;
	end if;
    if not IsDivisibleBy(l0 * sum^2,gcd^2) then 
		return false,_;
	end if;
    newwts:=[Integers() | l0 * wts[i] : i in face];
    Append(~newwts,sum^2);
    for i in [j : j in [1..#wts] | j ne base and not j in face] do
        Append(~newwts,sum * wts[i]);
    end for;
    redwts:=[Integers()|];
    for wt in newwts do
        bool,rwt:=IsDivisibleBy(wt,gcd);
        if not bool then return false,_; end if;
        Append(~redwts,rwt);
    end for;
    if GCD(redwts) ne 1 then return false,_; end if;
    Sort(~redwts);
    return true,redwts;
end function;


//Returns true iff the mutation specified is WPS to WPS
function mutation_exists(wts,bottom_face,top_vertex)
    //returns a bool of whether a mutation of WPS to WPS exists
    bottom_face_fixed:=bottom_face[1];
    Remove(~bottom_face,1);
    V:=Vertices(PolytopeOfWPS(wts));
    new_vertices:=[V[i] : i in [1..#wts] | not i in bottom_face];
    M:=Matrix(Rationals(),V);
    v:=ZeroSequence(Rationals(),#wts);
    //Now make w integral s.t. hmin, hmax coprime (is unique)
    sumli:=&+[wts[i] : i in bottom_face]+wts[bottom_face_fixed];
    g:=GCD(sumli,wts[top_vertex]);
    n:=wts[top_vertex]/g;
    m:=sumli/g;
    for i in bottom_face do
        v[i]:=-n;
    end for;
    v[bottom_face_fixed]:=-n;
    v[top_vertex]:=m;
    try 
        w:=Solution(Transpose(M),Matrix([v]));
    catch e
        return false;
    end try;
    //Now is the new guy via w a lattice polytope?
    for i in bottom_face do
        if not IsIntegral((1/n)*(V[i]-V[bottom_face_fixed])) then
                return false;
        else
            Append(~new_vertices,(m/n)*(V[i]-V[bottom_face_fixed]));
        end if;
    end for;
    //Check if the new guy really is WPS
    if Index(new_vertices) ne 1 then
        return false;
    else
        return true;
    end if;
end function;

//Returns all possible one step mutations of a WPS to a WPS
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

//Mutates a WPS about a single vertex and can implement existence check
function mutate_on_vertex(wts, bottom_face, top_vertex : verification:=true )
    //Returns mutated weights if going to WPS, false if no mutation exists.
    if verification and not mutation_exists(wts,bottom_face,top_vertex) then
        return false,_;
    end if;
    k:=#bottom_face;
    sumli:=&+[wts[i] : i in bottom_face];
    new_wts:=[];
    for i in [1..#wts] do
        if i eq top_vertex then
            Append(~new_wts,sumli^2);
        elif i in bottom_face then
            Append(~new_wts,wts[i]*wts[top_vertex]);
        else
            Append(~new_wts, wts[i]*sumli);
        end if;
    end for;
    out:=Sort([(w*sumli^(k-2))/(wts[top_vertex]^(k-1)) : w in new_wts]);
    try
        ChangeUniverse(~out,Integers());
    catch e
        return false,_;
    end try;
    if verification then
        return true,out;
    else
        return out;
    end if;
end function;

//Checks if a WPS is canonical, using [Kas09], returns the failing k-value
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

//Check if the k-value proves the WPS is not canonical using [Kas09]
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

//Checks if a WPS is terminal, using [Kas09], returns the failing k-value
function is_terminal(wts)
    Sort(~wts);
    h:=&+wts;
    n:=#wts - 1;
    for k in [2..h - 2] do
        s:=&+[(wt * k) mod h : wt in wts];
        s:= s/h;
        if s lt 2 or s gt n-1 then
            return k;
        end if;
    end for;
    return true;
end function;

//Code to check if this k-value proves this WPS is not terminal as in [Kas09]
function breaks_terminal_on_k(wts,k)
    Sort(~wts);
    wts:=[Integers()!w : w in wts];
    h:=&+wts;
    n:=#wts - 1;
    s:=&+[(wt * k) mod h : wt in wts];
    s:= s/h;
    if s lt 2 or s gt n-1 then
        return true;
    end if;
    return false;
end function;

//Calculates mutations tree of a WPS
function mutation_tree(n,max_depth,seed)
    graph:=[];
    parent:=[0];//so the nth list of weights in graph came from the parent[n]'th guy in the previous block of graph
    parent:=parent cat [1 : i in [3..n+1]];
    former:=[seed];
    current:=[mutate(seed,[2,i],1: verification:=false) : i in [3..n+1]];
    next:=[];
    depth:=2;
    while depth le max_depth do
        print current;
        for wts in current do
            for s in Subsets({1..n+1},2) do
                l:=[i: i in s];
                for t in [1..n] do
                    if not t in l then
                        bool,new_wts:=mutate(wts,l,t);
                        if bool and not new_wts in former then
                            Append(~next,new_wts);
                            Append(~parent,Index(current,wts));
                        end if;
                    end if;
                end for;
            end for;
        end for;
        depth:=depth+1;
        Append(~graph,former);
        former:=current;
        current:=next;
        next:=[];
    end while;
    Append(~graph,former);
    Append(~graph, current);
    return graph,parent;
end function;

