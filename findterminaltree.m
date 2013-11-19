//Code to calculate the mutation tree of the (conjectured) maximal
//WPS when restricting to WPS->WPS
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

function mutate(wts, bottom_face, top_vertex : verification:=true )
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

function mutation_tree(n,max_depth,seed)
    graph:=[];
    parent:=[0];//so the nth list of weights in graph came from the parent[n]'th guy in the previous block of graph
    former:=[];
    current:=[seed];//TODO, mark off parents
    next:=[];
    depth:=1;
    print "______________";
    print "X_0";
    print seed;
    while depth le max_depth do
        print "________________";
        print "X_",depth;
        for wts in current do
            wts_set:=Set(wts);
            for s in Subsets({1..n+1},2) do //TODO: currently just edges
                l:=[i: i in s];
                for t in wts_set do
                    top_guy:=Index(wts,t);
                    if not top_guy in l then
                        bool,new_wts:=mutate(wts,l,top_guy);
                        if bool and not new_wts in former then
                            Append(~next,new_wts);
                            Append(~parent,Index(current,wts));
                            print new_wts;
                            print "Parent:", Index(current,wts);
                            print "Bottom Edge:",l;
                            print "Top Vertex:",top_guy;
                            print "Breaks Terminal On 'h':",breaks_terminal_on_k(new_wts,&+wts);
                            print "---------";
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
        print mutation_tree(n,max_depth,maximum_terminal(n));
    end for;
    return true;
end function;

TerminalWPSMutationTree(5,10);
