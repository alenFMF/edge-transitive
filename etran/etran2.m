load "etran/t2.m";

t1olst := [**];
t2exlst := [**];
t3lst := [**];
t4lst := [**];
t5lst := [**];

/**
 * author: Alen Orbanic
 * The package contains a database of non-degenerate edge-transitive maps.
 * A map is presented as [T,L,R], where T,L,R are three involutions, (TL)^2 = 1.
 * 
 * Main functions.
 * mp := getMap(19, "PD", "2");
 * getMapInfo(mp);
 *>[ edges, genus, symbol, type, iso ]
 *>[* 2P, -5, 12, [* 4, 8, [* 3, 4 *] *], [* 1, 2, 3, 4, 5, 6 *] *]
 */

//Constants
type1 := "1";
type2 := "2";
type2D := "2D";
type2P := "2P";
type2ex := "2ex";
type2exD := "2exD";
type2exP := "2exP";
type3 := "3";
type4 := "4";
type4D := "4D";
type4P := "4P";
type5 := "5";
type5D := "5D";
type5P := "5P";


//Auxiliary function
function mod1(n, md)
     x := (n + 2*md) mod md;
     if x eq 0 then return md; end if;
     return x;
end function;

//Auxiliary function
function changeGroup(gr, ty)
   if ty eq "1" then
     O<r,l> := Group<r,l |l^2>;
     F<T,L,R> := Group<T,L,R| T^2, L^2, R^2, (T*L)^2>;
     hom1 := hom<O->gr| gr.1, gr.2>;
     hom2 := hom<O->F|R*T, T*L>;   
   elif ty eq "2" then
     O<t,x,y> := Group<t,x,y |t^2, x^2, y^2>;
     F<T,L,R> := Group<T,L,R| T^2, L^2, R^2, (T*L)^2>;
     hom1 := hom<O->gr| gr.1, gr.2, gr.3>;
     hom2 := hom<O->F|T, R, L*R*L>;
   elif ty eq "2ex" then
     O<f,t> := Group<f,t |t^2>;
     F<T,L,R> := Group<T,L,R| T^2, L^2, R^2, (T*L)^2>;
     hom1 := hom<O->gr| gr.1, gr.2>;
     hom2 := hom<O->F|L*R, T>;   
   elif ty eq "3" then
     O<a,b,c,d> := Group<a,b,c,d |a^2, b^2, c^2, d^2>;
     F<T,L,R> := Group<T,L,R| T^2, L^2, R^2, (T*L)^2>;
     hom1 := hom<O->gr| gr.1, gr.2, gr.3, gr.4>;
     hom2 := hom<O->F|R, L*R*L, T*R*T, T*L*R*L*T>;      
   elif ty eq "4" then
     O<s,x,y> := Group<s,x,y |x^2, y^2>;
     F<T,L,R> := Group<T,L,R| T^2, L^2, R^2, (T*L)^2>;
     hom1 := hom<O->gr| gr.1, gr.2, gr.3>;
     hom2 := hom<O->F|R*T, L*R*L, T*L*R*L*T>;
   else //type eq 5
     O<a,b> := Group<a,b |>;
     F<T,L,R> := Group<T,L,R| T^2, L^2, R^2, (T*L)^2>;
     hom1 := hom<O->gr| gr.1, gr.2>;
     hom2 := hom<O->F|R*T, L*T*R*L>;
   end if;
     H := Kernel(hom1);
     H2 := hom2(H);
     _,b,_ := CosetAction(F, H2);
     return GeneratorsSequence(b);
end function; 

/**
 * Returns map involutions T,L,R from the map mp in the presentation [T,L,R]
 */
function getMapInvolutions(mp)
     return mp[1], mp[2], mp[3];
end function;

/**
 * Returns the set of flags for the map mp in the presentation [T,L,R]
 */
function getFlags(mp)
     sup := Support(mp[1]) join Support(mp[2]) join Support(mp[3]);
     if #sup eq 0 then return {1}; end if;
     return {@ i: i in [1 .. #sup] @};
end function;


function getNumberOfFlags(mp)
     return #getFlags(mp);
end function;


function getNumberOfEdges(mp)
     T, L, R := getMapInvolutions(mp);
     n := getNumberOfFlags(mp);
     return #Orbits(sub<SymmetricGroup(n)| T, L>);
end function;

/**
 * Returns true if the map mp in the presentation [T, L, R] is orientable.
 */
function isOrientable(mp)
  flags := getFlags(mp);
  n := #flags;
  T, L, R := getMapInvolutions(mp);
  grp := sub<SymmetricGroup(n)| T, L, R>;
  ori := sub<grp| R*T, L*R>;
  if #Orbits(ori) eq 1 then return false;
  else return true; end if;
end function;


/**
 * Returns Dual of  the map mp of the form [T, L, R]
 */
function DualOfMap(mp)
     return [ mp[2], mp[1], mp[3]];
end function;

/**
 * Returns Petrie dual of the map mp of the form [T, L, R]
 */
function PetrieOfMap(mp)
     return [ mp[1], mp[1]*mp[2], mp[3] ];
end function;


/** 
 *  Given the id of the map (n), a transformation (tran - "D", "P" or "PD") and 
 *  its basic type (type - "1", "2", "2ex", "3", "4", "5") it returns the map
 *  in presentation [T, L, R].
 */
function getMap(n, tran, ty)
    if ty eq "1" then
       lst := t1olst;
    
    elif ty eq "2" then
       lst := t2lst;
    elif ty eq "2ex" then
       lst := t2exlst;
    elif ty eq "3" then
       lst := t3lst;
    elif ty eq "4" then
       lst := t4lst;
    else 
       lst := t5lst;
    end if;
    gr := lst[n];    
    //mp :=getMapFromGroup(grx, ty);
    mp := changeGroup(gr, ty);
    if (tran eq "D") then 
       mp2 := DualOfMap(mp);
    elif tran eq "P" then
       mp2 := PetrieOfMap(mp);
    elif tran eq "PD" then
       mp2 := PetrieOfMap(DualOfMap(mp));
    elif tran eq "" then
       mp2 := mp;
    else 
       print("Wrong arg[2]!");
       mp2 := 0;
    end if;
    return mp2;
end function;


/**
 * Returns the genus of the map mp. If the number is negative it represents non-orientable genus.
 */
function getMapGenus(mp)
        flags := getFlags(mp);
        n := #flags;
        E := n div 4;
        T, L, R := getMapInvolutions(mp);
        
        orbv :=  Orbits(sub<SymmetricGroup(n)| T*R>);
        orbf :=  Orbits(sub<SymmetricGroup(n)| L*R>);
        V := #orbv div 2;
        F := #orbf div 2;
        if isOrientable(mp) then
  	   return (2 - (V - E + F)) div 2;
           if (2 - (V - E + F)) mod 2 ne 0 then
	      print "getMapGenus::error!!!";
              return 0;
	   end if;
        else 
           return -(2 - (V - E + F));
        end if;
end function;



/**
 * Returns medial of a map.
 */
function MedialOfMap(mp)
     n := #getFlags(mp);
     fun1 := map<car<{1 .. n}, {0,1}> -> {1 .. 2*n}| x :-> x[1] + n*x[2]>;
     fun1inv := map<{1 .. 2*n} -> car<{1 .. n}, {0, 1}>|x :-> <mod1(x,n), (x-1) div n> >;
     function funT(x)
        tmp := fun1inv(x);
        return fun1(<tmp[1], (tmp[2]+1) mod 2>);
     end function;
     function funL(x)
        tmp := fun1inv(x);
        return fun1(<tmp[1]^mp[3], tmp[2]>);
     end function;
     function funR(x)
        tmp := fun1inv(x);
        if(tmp[2] eq 0) then
           return fun1(<tmp[1]^mp[2], tmp[2]>);
        else
           return fun1(<tmp[1]^mp[1], tmp[2]>);
        end if;
     end function;
     Sn := SymmetricGroup(2*n);
     T := Sn![funT(i) :i in [1 .. 2*n]];
     L := Sn![funL(i) :i in [1 .. 2*n]];
     R := Sn![funR(i) :i in [1 .. 2*n]];  
     return [* T, L, R *];
end function;

//Auxiliary  function - not very efficient!
function getMapAutGraph(mp)
  flags := getFlags(mp);
  n := #flags;
  //first n vertices are flags
  V := flags;
  T, L, R := getMapInvolutions(mp);
  orbv :=  Orbits(sub<SymmetricGroup(n)| T*R>);
  numv := #orbv;
  curv := n + 1;
  //then the next vertices are real vertices
  V := V join {@ i: i in [n + 1 .. n + numv] @};
  orbe := Orbits(sub<SymmetricGroup(n)| T, L>);
  nume := #orbe;
  cure := n + numv + 1; 
  // and the next vertices are edges
  V := V join {@ i: i in [n + numv + 1 .. n + numv + nume] @};
  tse := {Set(i): i in Orbits(sub<SymmetricGroup(n)| T>)};
  lse := {Set(i): i in Orbits(sub<SymmetricGroup(n)| L>)};
  rse := {Set(i): i in Orbits(sub<SymmetricGroup(n)| R>)};
  E := {@ @};
  //each vertex vertex is connected to corresponding flag vertices
  for i in orbv do
     st := Set(i);
     E := E join {{curv, k}: k in i};
     curv := curv + 1;   
  end for;
  //each edge vertex is connected to corresponding flag vertices
  for i in orbe do
     st := Set(i);
     E := E join {{cure, k}: k in i};
     cure := cure + 1;   
  end for;
  // all edges from action graph of map are added
  fixtse := {x: x in tse| #x eq 2}; 
  fixlse := {x: x in lse| #x eq 2}; 
  fixrse := {x: x in rse| #x eq 2}; 
     //E := E join tse join lse join rse;
  E := E join fixtse join fixlse join fixrse;
  gr := Graph<V | E>;
//function that assigns the names to vertices
  fn := function(xx)
     if xx le n then return "f";
     elif (xx gt n) and (xx le n + numv) then return "v";
     else return "e";
     end if;
  end function;
     //asigning labels to vertices
     asnl := [fn(Index(i)): i in VertexSet(gr)];
     AssignLabels(VertexSet(gr), asnl);
     return gr;
end function;

/**
 * Returns map's automorphism group.
 */
function getAutomorphismGroup(mp)
     gr := getMapAutGraph(mp);
     n := getNumberOfFlags(mp);
     ag := AutomorphismGroup(gr);
     gs := GSet(ag);
     actmap := Action(gs);
     ss := GSet(ag, Set([1 .. n]), actmap);
     _,L,_ := Action(ag, ss);
     return L;
end function;  

/**
 * If the map mp is edge-transitive then it return maps type.
 * Otherwise the string "Error!" is returned.
 */
function getMapType(mp)
     n := #getFlags(mp);
     ag := getAutomorphismGroup(mp);
     o := Order(ag);
     if o eq n then return type1; end if;
     T, L, R := getMapInvolutions(mp);
     orb := Orbits(ag);
     for i in orb do 
       st := Set(i);
       if 1 in st then break; end if;
     end for;
     if o eq (n div 2) then
        if 1^T in st then 
           if 1^R in st then return type2; else return type2ex; end if;
        end if;
        if 1^L in st then 
           if 1^R in st then return type2D; else return type2exD; end if;
        end if;
        if 1^(L*T) in st then 
           if 1^R in st then return type2P; else return type2exP; end if;
        end if;
     else
        if 1^R in st and 1^(L*R*L) in st then return type3; end if;
        if (1^R in st and 1^(L*R*L*T) in st) or (1^(L*R*L) in st and 1^(R*T) in st) then return type4; end if;
        if (1^R in st and 1^(T*L*R*T) in st) or (1^(T*R*T) in st and 1^(L*R) in st) then return type4D; end if;
        if (1^R in st and 1^(T*L*T*R*T) in st) or (1^(T*L*R) in st and 1^(L*R*L) in st) then return type4P; end if;
        if 1^(R*T) in st then return type5; end if;
        if 1^(L*R) in st then return type5D; end if;
        if 1^(T*L*R) in st then return type5P; end if;
        print "Strange type";
     end if;   
     return "Error!";  
end function;


/**
 * Returns the map symbol of the map mp.
 */ 
function getMapSymbol(mp)
    T, L, R := getMapInvolutions(mp);
    n := #getFlags(mp);
    type := getMapType(mp);
       if type eq type1 or type eq type2ex then
       a := Order(T*R);
       b := Order(L*R);
       c := Order(T*L*R);
       return [* a, b, c *];
    elif type eq type3 then

       orb := Orbits(sub<SymmetricGroup(n)| T*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       a := #st;
       j := 1^L;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       aa := #st;
   
       orb := Orbits(sub<SymmetricGroup(n)| L*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       b := #st;
       j := 1^T;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       bb := #st;

       orb := Orbits(sub<SymmetricGroup(n)| T*L*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       c := #st;
       j := 1^T;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       cc := #st; 
       return [* [*a, aa*], [*b, bb*], [*c, cc*] *];
    elif type eq type2 then
       orb := Orbits(sub<SymmetricGroup(n)| T*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       a := #st;
       j := 1^L;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       aa := #st;
       b := Order(L*R);
       c := Order(T*L*R);
       return [* [*a, aa*],  b, c *];
    elif type eq type2D then
       a := Order(T*R);
       orb := Orbits(sub<SymmetricGroup(n)| L*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       b := #st;
       j := 1^T;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       bb := #st;
       c := Order(T*L*R);
       return [* a, [*b, bb*], c *];
    elif type eq type2P then
       a := Order(T*R);
       b := Order(L*R);
       orb := Orbits(sub<SymmetricGroup(n)| T*L*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       c := #st;
       j := 1^T;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       cc := #st; 
       return [* a, b, [*c, cc*] *];
    elif type eq type2ex then
       a := Order(T*R);
       b := Order(L*R);
       c := Order(T*L*R);
       return [* a, b, c *];
    elif type eq type2exD then 
       a := Order(T*R);
       b := Order(L*R);
       c := Order(T*L*R);
       return [* a, b, c *];
    elif type eq type2exP then 
       a := Order(T*R);
       b := Order(L*R);
       c := Order(T*L*R);
       return [* a, b, c *];
    elif type eq type4 then 
       orb := Orbits(sub<SymmetricGroup(n)| T*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       a := #st;
       j := 1^L;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       aa := #st;
       b := Order(L*R);
       c := Order(T*L*R);
       return [* [*a, aa*],  b, c *];
    elif type eq type4D then 
       a := Order(T*R);
       orb := Orbits(sub<SymmetricGroup(n)| L*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       b := #st;
       j := 1^T;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       bb := #st;
       c := Order(T*L*R);
       return [* a, [*b, bb*], c *];
    elif type eq type4P then
       a := Order(T*R);
       b := Order(L*R);
       orb := Orbits(sub<SymmetricGroup(n)| T*L*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       c := #st;
       j := 1^T;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       cc := #st; 
       return [* a, b, [*c, cc*] *];
    elif type eq type5 then
       orb := Orbits(sub<SymmetricGroup(n)| T*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       a := #st;
       j := 1^L;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       aa := #st;
       b := Order(L*R);
       c := Order(T*L*R);
       return [* [*a, aa*],  b, c *];
    elif type eq type5D then
       a := Order(T*R);
       orb := Orbits(sub<SymmetricGroup(n)| L*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       b := #st;
       j := 1^T;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       bb := #st;
       c := Order(T*L*R);
       return [* a, [*b, bb*], c *];
    elif type eq type5P then
       a := Order(T*R);
       b := Order(L*R);
       orb := Orbits(sub<SymmetricGroup(n)| T*L*R>);
       for i in orb do
         st := Set(i);
         if 1 in st then break; end if;
       end for;
       c := #st;
       j := 1^T;
       for i in orb do
         st := Set(i);
         if j in st then break; end if;
       end for;
       cc := #st; 
       return [* a, b, [*c, cc*] *];
    else
       print "Error";
       return 0;
    end if;
    return 0;
end function;


function IsMapIsomorphic(m1, m2)
     n1 := getNumberOfFlags(m1);
     n2 := getNumberOfFlags(m2);
     if n1 ne n2 then return false, 0; end if;
     gr1 := getMapAutGraph(m1);
     gr2 := getMapAutGraph(m2);
     t := IsIsomorphic(gr1, gr2);
     return t;
end function;


function getTrialityMaps(mp)
    return  [* mp, DualOfMap(mp), PetrieOfMap(mp), PetrieOfMap(DualOfMap(mp)), DualOfMap(PetrieOfMap(mp)), DualOfMap(PetrieOfMap(DualOfMap(mp))) *];  
end function;


function getIsomorphicsInTriality(mp)
     out := [* *];
     lst := getTrialityMaps(mp);
     for i in [1 .. #lst] do
        isiso := 0;
        for j in [1 .. i - 1] do
	       if IsMapIsomorphic(lst[i], lst[j]) then
   	           isiso := j;
   	           break;
               end if;
        end for;
        if isiso gt 0 then 
           Append(~out, isiso);
        else 
           Append(~out, i);                
        end if;                 
     end for;
     return out;  
end function;


function getMapInfo(mp)
    print "[ edges, genus, symbol, type, iso ]";
    return [*  getMapType(mp), getMapGenus(mp),getNumberOfEdges(mp), getMapSymbol(mp), getIsomorphicsInTriality(mp)*];
end function;


Sn1 := SymmetricGroup(1);
typs1 := [*
[*"1",		Sn1!Id(Sn1), 	Sn1!Id(Sn1), 	Sn1!Id(Sn1)*]
*];

Sn2 := SymmetricGroup(2);
typs2 := [*
[*"2_0",		Sn2!Id(Sn2), 	Sn2!(1,2), 	Sn2!(1,2)*],
[*"2_2",		Sn2!(1,2), 	Sn2!(1,2), 	Sn2!Id(Sn2)*],
[*"2",			Sn2!(1,2), 	Sn2!(1,2), 	Sn2!(1,2)*],
[*"2_01",		Sn2!Id(Sn2), 	Sn2!Id(Sn2), 	Sn2!(1,2)*],
[*"2_1",		Sn2!(1,2),	Sn2!Id(Sn2), 	Sn2!(1,2)*], 
[*"2_12",		Sn2!(1,2),	Sn2!Id(Sn2),	Sn2!Id(Sn2)*],
[*"2_02",		Sn2!Id(Sn2), 	Sn2!(1,2), 	Sn2!Id(Sn2)*]
*];

Sn3 := SymmetricGroup(3);
typs3 := [*
[*"3_0",		Sn3!Id(Sn3),  	Sn3!(1,3), 	Sn3!(1,2)*],
[*"3_2",		Sn3!(1,2),  	Sn3!(1,3), 	Sn3!Id(Sn3)*],
[*"3_02",		Sn3!(1,2), 	Sn3!(1,3), 	Sn3!(1,2)*]
*];

Sn4 := SymmetricGroup(4);
typs4 := [*
[*"4_A",		Sn4!Id(Sn4), 	Sn4!(1,3)(2,4), Sn4!(1,2)*],
[*"4_Ad",		Sn4!(1,2),	Sn4!(1,3)(2,4), Sn4!Id(Sn4)*],
[*"4_Ap",		Sn4!(1,2), 	Sn4!(1,3)(2,4), Sn4!(1,2)*],
[*"4_B",		Sn4!Id(Sn4), 	Sn4!(1,3), 	Sn4!(1,2)(3,4)*],
[*"4_Bd",		Sn4!(1,2)(3,4), Sn4!(1,3), 	Sn4!Id(Sn4)*],
[*"4_Bp",		Sn4!(1,2)(3,4), Sn4!(1,3), 	Sn4!(1,2)(3,4)*], 
[*"4_C",		Sn4!Id(Sn4), 	Sn4!(1,3)(2,4), Sn4!(1,2)(3,4)*],
[*"4_Cd",		Sn4!(1,2)(3,4), Sn4!(1,3)(2,4), Sn4!Id(Sn4)*],
[*"4_Cp",		Sn4!(1,2)(3,4), Sn4!(1,3)(2,4), Sn4!(1,2)(3,4)*], 
[*"4_D",		Sn4!(1,2)(3,4), Sn4!(1,3), 	Sn4!(1,2)*],
[*"4_Dd",		Sn4!(1,2), 	Sn4!(1,3), 	Sn4!(1,2)(3,4)*],
[*"4_Dp",		Sn4!(1,2), 	Sn4!(1,3), 	Sn4!(3,4)*], 
[*"4_E",		Sn4!(1,2)(3,4), Sn4!(1,3)(2,4), Sn4!(1,2)*],
[*"4_Ed",		Sn4!(1,2), 	Sn4!(1,3)(2,4), Sn4!(1,2)(3,4)*],
[*"4_Ep",		Sn4!(1,2), 	Sn4!(1,3)(2,4), Sn4!(3,4)*], 
[*"4_F",		Sn4!(1,2)(3,4), Sn4!Id(Sn4),	Sn4!(1,3)(2,4)*], 
[*"4_G",		Sn4!(1,2)(3,4), Sn4!(1,2)(3,4), Sn4!(1,3)(2,4)*],
[*"4_Gd",		Sn4!(1,2)(3,4), Sn4!(1,3)(2,4), Sn4!(1,3)(2,4)*],
[*"4_Gp",		Sn4!(1,2)(3,4), Sn4!(1,4)(2,3), Sn4!(1,3)(2,4)*], 
[*"4_H",		Sn4!(1,2)(3,4), Sn4!(1,2), 	Sn4!(1,3)(2,4)*],
[*"4_Hd",		Sn4!(1,2)(3,4), Sn4!(1,3), 	Sn4!(1,3)(2,4)*],
[*"4_Hp",		Sn4!(1,2)(3,4), Sn4!(1,4), 	Sn4!(1,3)(2,4)*]
*];

typsXX := [typs1, typs2, typs3, typs4];

typs := [* *];
for lst in typsXX do
	nlst := [**];
	for el in lst do
		mpt := [*el[4], el[2], el[3]*];
		n := getNumberOfFlags(mpt);
		Sn := SymmetricGroup(n);
		Append(~nlst, [*el[1], sub<Sn|el[2], el[3], el[4]>*]);
	end for;
	Append(~typs, nlst);
end for;

function gwType(type)
	if type eq "1" then 
		return "1";
	elif type eq "2_01" then
		return "2D";
	elif type eq "2_12" then
		return "2";
	elif type eq "2_1" then
		return "2P";
	elif type eq "4_F" then
		return "3";
	elif type eq "2_0" then
		return "2exD";
	elif type eq "2_2" then
		return "2ex";
	elif type eq "2" then
		return "2exP";
	elif type eq "4_G" then
		return "5D";
	elif type eq "4_Gd" then
		return "5";
	elif type eq "4_Gp" then
		return "5P";
	elif type eq "4_H" then
		return "4D";
	elif type eq "4_Hd" then
		return "4";
	elif type eq "4_Hp" then
		return "4P";
	else
		return "-";
	end if;
end function;

function permutationIso(g1, g2)
	b, m := IsHomomorphism(g1, g2, GeneratorsSequence(g2));
	if not b then
		return false;
	end if;
	stab1 := Stabilizer(g1, 1);
	stab2 := Stabilizer(g2, 1);
	fstab := m(stab1);
	return IsConjugate(g2, fstab, stab2); 
end function;

function newIso(mp1, mp2)
	T1, L1, R1 := getMapInvolutions(mp1);
	T2, L2, R2 := getMapInvolutions(mp2);
	n1 := getNumberOfFlags(mp1);
	n2 := getNumberOfFlags(mp2);
	if n1 ne n2 then return false; end if;
	Sn := SymmetricGroup(n1);
	return permutationIso(sub<Sn|L1, R1, T1>, sub<Sn| L2, R2, T2>);
end function;

function recognizeType(mp)
	T, L, R := getMapInvolutions(mp);
	n := getNumberOfFlags(mp);
	Sn := SymmetricGroup(n);
	G := sub<Sn|L, R, T>;
	stab := Stabilizer(G, 1);
	norm := Normalizer(G, stab);
        ind := Index(G, norm);
        if ind gt 4 then return "-"; end if;
        typx := typs[ind];
        _,b,_ := CosetAction(G, norm);
 	for cand in typx do
 		gp := cand[2];
 		if permutationIso(b, gp) then
 			return cand[1];
 		end if;
 	end for;        
	return "Error in types!";	
end function;

function deMedialize(mp)
   S2, S0, S1 := getMapInvolutions(mp);
   n := getNumberOfFlags(mp);
   Sn := SymmetricGroup(n);
   st := {#o: o in Orbits(sub<Sn|S2, S1>)};
   if not (#st eq 1 and Random(st) eq 8) then
   	return false, [**];
   end if;
   G := sub<Sn| S0, S1, S2>;
   stab := Stabilizer(sub<Sn|S0, S1, S2>, 1);
   G2014 := sub<Sn| S1, S0, S2*S1*S2>;
   if not (Index(G, G2014) eq 2 and stab subset G2014) then
   	return false, [**];
   end if;
   _,b,_ := CosetAction(G2014, stab);
   seq := GeneratorsSequence(b);
   return true, [*seq[3], seq[1], seq[2]*];
end function;


function pathsToOrbits(G, stab, norm, fmap, b)
	s0 := G.1;
	s1 := G.2;
	s2 := G.3;
	stab1 := Stabilizer(b, 1);
	stabmap := fmap(norm);
	n2 := Index(b, stab1);
	root := 1;
	rootcheck := true;	
	if not stabmap eq stab1 then 
		rootcheck := false;
		print("Stabilizer shift"); 
		for i in [2 .. n2] do
			if stabmap eq Stabilizer(b, i) then
				root := i;
				rootcheck := true;
				break;
			end if;
		end for;
	end if;
	if not rootcheck then 
		print("Error in matching stabilizer."); 
		return 0;
	end if;
	Q := [root];
	visitedW := [Id(G): j in [1 .. n2]];
	visitedT := [0: j in [1 .. n2]];
	visited := {root};
	while #Q gt 0 do
		tmp := Q[1];
		Remove(~Q, 1);
		for w in [s0, s1, s2] do
			tar := tmp^fmap(w);
			if tar in visited then continue; end if;
			Include(~visited, tar);
			Append(~Q, tar);
			visitedW[tar] := visitedW[tmp]*w;
		end for;
	end while;
	return root, visitedW;
end function;




function orbitsOfFacesRepresentatives(G, stab, norm, fmap, b, gens)
	root, visitedW := pathsToOrbits(G, stab, norm, fmap, b);
	fgens := [fmap(g): g in gens];
	sub := sub<b|fgens>;
	orbs := Orbits(sub);
	choice := [root];
	for o in orbs do
		if root in o then
			continue;
		else
			Append(~choice, Random(o));
		end if;
	end for;
	return [1^visitedW[c]: c in choice];
end function;

function orbitsOfFaces(G, stab, norm, fmap, b, gens)
	choice := orbitsOfFacesRepresentatives(G, stab, norm, fmap, b, gens);
	subOrig := sub<G|gens>; 
	return [#Orbit(subOrig, c) div 2: c in choice], choice;
end function;

//Reps defines flag representatives for each orbit of vertices.
//For each representative vertex we calculate max edge multiplicity to neighbours.
//Max over all orbits is returned. Multiple loops on a vertex are also considered as 
//a multiple edge.
function maxEdgeMultiplicity(G, reps)
	s0 := G.1; s1 := G.2; s2 := G.3;
	vg := sub<G|s1, s2>;
	eg := sub<G|s0, s2>;
	maxem := 1;
	for fg in reps do
		v1 := Orbit(vg, fg);
		other := {ff^s0: ff in v1};
		for fff in other do
			v2 := Orbit(vg, fff);
			maxem := Max(maxem, #(other meet v2) div 2);
		end for;
	end for;
	return maxem;
end function;

infoHead := 
"#flagOrbs"
*";"*"Type"
*";"*"GW type"
*";"*"|V|"
*";"*"#vorb"
*";"*"vorb sizes" 
*";"*"|E|"
*";"*"#eorb"
*";"*"eorb sizes"	
*";"*"max EM"
*";"*"|F|"
*";"*"#forb"
*";"*"forb sizes" 
*";"*"|P|"
*";"*"#porb"
*";"*"porb sizes";



//For a given map it returns a comma separated list of parameters
function getMapInfo2(mp)
	T, L, R := getMapInvolutions(mp);
	n := getNumberOfFlags(mp);
	Sn := SymmetricGroup(n);
	G := sub<Sn|L, R, T>;
	s0 := G.1; s1 := G.2; s2 := G.3;
	stab := Stabilizer(G, 1);
	norm := Normalizer(G, stab);
	fmap, b, _ := CosetAction(G, norm);
	
	type := recognizeType(mp);
	k := Index(G, norm);
	gwtype := gwType(type);
	v := Orbits(sub<G|s1, s2>);
	e := Orbits(sub<G|s0, s2>);
	f := Orbits(sub<G|s0, s1>);
	p := Orbits(sub<G|s0*s2, s1>);
	vv,reps := orbitsOfFaces(G ,stab, norm, fmap, b, [s1, s2]);
	ve,_ := orbitsOfFaces(G ,stab, norm, fmap, b, [s0, s2]);
	mex := maxEdgeMultiplicity(G, reps);
	vf,_ := orbitsOfFaces(G ,stab, norm, fmap, b, [s0, s1]);
	vp,_ := orbitsOfFaces(G ,stab, norm, fmap, b, [s0*s2, s1]);
	out := IntegerToString(k)*";"* 	//Number of flag orbits
	       type*";"*	       	//Map type if available
	       gwtype*";"*		//GW type if available (if edge transitive)
	       IntegerToString(#v)*";"*	//Number of vertices
	       IntegerToString(#vv)*";"*//Number of vertex orbits
	       Sprint(vv)*";"*		//Sizes of vertices in vertex orbits 
	       IntegerToString(#e)*";"*	//Number of edges
	       IntegerToString(#ve)*";"*//Number of edge orbits
	       Sprint(ve)*";"*		//Sizes of edges in edge orbits	
	       IntegerToString(mex)*";"*//Maximal edge multiplicity in the map between two vertices (same (loops) or different (parallel edges))
	       IntegerToString(#f)*";"*	//Number of faces
	       IntegerToString(#vf)*";"*//Number of face orbits
	       Sprint(vf)*";"*		//Sizes of faces in face orbits 
	       IntegerToString(#p)*";"*	//Number of Petrie circuits
	       IntegerToString(#vp)*";"*//Number of Petrie circuit orbits
	       Sprint(vp);		//Sizes of Petrie circuits in vertex orbits 
	return out;
end function;

demedHead := " ID;tran;GW;map symb;genus; EM;"*infoHead;

function mapSymbolString(mp)
	st := "<";
	sy := getMapSymbol(mp);
	if Type(sy[1]) eq RngIntElt then st *:= IntegerToString(sy[1]); 
	else st *:= IntegerToString(sy[1][1])*","*IntegerToString(sy[1][2]); end if; 
	st *:= "|";
	if Type(sy[2]) eq RngIntElt then st *:= IntegerToString(sy[2]); 
	else st *:= IntegerToString(sy[2][1])*","*IntegerToString(sy[2][2]); end if;
 	st *:= "|";
	if Type(sy[3]) eq RngIntElt then st *:= IntegerToString(sy[3]);
	else st *:= IntegerToString(sy[3][1])*","*IntegerToString(sy[3][2]); end if;
	return st*">";
end function;

function demedialization(idnum, tran, ty) 
	mp := getMap(idnum, tran, ty);
	ok, dmap := deMedialize(mp);
	if not ok then return ""; end if;
	T, L, R := getMapInvolutions(mp);
	n := getNumberOfFlags(mp);
	Sn := SymmetricGroup(n);
	G := sub<Sn|L, R, T>;
	s0 := G.1; s1 := G.2; s2 := G.3;
	stab := Stabilizer(G, 1);
	norm := Normalizer(G, stab);
	fmap, b, _ := CosetAction(G, norm);
	
	vv,reps := orbitsOfFaces(G ,stab, norm, fmap, b, [s1, s2]);
	mex := maxEdgeMultiplicity(G, reps);
	st := IntegerToString(idnum)*";"*tran*";"*getMapType(mp)*";"*Sprint(mapSymbolString(mp))*";"
		*IntegerToString(getMapGenus(mp))*";"*IntegerToString(mex)*";";
	if not ok then return st; end if;
	return st*getMapInfo2(dmap);
end function;

procedure demedialization2ToFile(fname, ty, nstart, nend)
	F := Open(fname, "wt");
	Puts(F, demedHead);
	for n in [nstart .. nend] do
		if n mod 500 eq 0 then
			print(Sprint(n)*"/"*Sprint(nend));
		end if;
	        st := demedialization(n, "", ty);
	        if #st gt 0 then Puts(F, st); end if;
 		st := demedialization(n, "D", ty);
		if #st gt 0 then Puts(F, st); end if;
		st := demedialization(n, "P", ty);
		if #st gt 0 then Puts(F, st); end if;
		st := demedialization(n, "PD", ty);			
		if #st gt 0 then Puts(F, st); end if;
	end for;
	F := 0;
end procedure;



print("Type 2");
demedialization2ToFile("type2.csv", "2", 1, #t2lst);
