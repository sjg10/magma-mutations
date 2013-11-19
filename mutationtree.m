function gcd_vect_entries(V)
    ChangeUniverse(~V,Integers());
    k:=V[1];
    for v in V do
        k:=GCD(k,v);
    end for;
    return k;
end function;


function mutation_exists_and_return_mult(wts,bottom_face,top_vertex)
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
        return false,_;
    end try;
    //Now is the new guy via w a lattice polytope?
    for i in bottom_face do
        if not IsIntegral((1/n)*(V[i]-V[bottom_face_fixed])) then
                return false,_;
        else
            Append(~new_vertices,(m/n)*(V[i]-V[bottom_face_fixed]));
        end if;
    end for;
    return true,Index(new_vertices);
end function;

function mutate(wts, bottom_face, top_vertex : verification:=true )
    //Given wts with index, returns mutated weights with index, false if no mutation exists.
    bool,ind :=  mutation_exists_and_return_mult(wts,bottom_face,top_vertex);
    if not bool then
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
    d:=gcd_vect_entries(new_wts);
    out:=Sort([(w/d) : w in new_wts]); 
    try
        ChangeUniverse(~out,Integers());
    catch e
        return false,_;
    end try;
    Append(~out,ind);
    if verification then
        return true,out;
    else
        return out;
    end if;
end function;

function mutation_tree(max_depth,seed)
    n:=#seed-1;
    Append(~seed,Index(Vertices(PolytopeOfWPS(seed))));
    graph:=[];
    parent:=[0];//so the nth list of weights in graph came from the parent[n]'th guy in the previous block of graph
    parent:=parent cat [1 : i in [3..n+1]];
    former:=[];
    current:=[seed];
    next:=[];
    depth:=1;
    while depth le max_depth do
        //print current;
        for wtswithind in current do
            wts:=wtswithind[1..#wtswithind-1];
            for k in [2..#wts-1] do
                for s in Subsets({1..n+1},k) do //TODO: currently just edges
                    l:=[i: i in s];
                    for t in [1..n] do
                        if not t in l then
                            bool,new_wts:=mutate(wts,l,t);
                            if bool and not new_wts in former then
                                Append(~next,new_wts);
                                Append(~parent,Index(current,wtswithind));
                                if new_wts[#new_wts] lt wtswithind[#wtswithind] then
                                    print wtswithind,new_wts,l,t;
                                end if;
                            end if;
                        end if;
                    end for;
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

G,P:=mutation_tree(3,[1,1,1,2]); 
