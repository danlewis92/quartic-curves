_<U0,U1,U2,U3,U4>:=PolynomialRing(Integers(),5);
BitangRelations:=[    U1^3 - 4*U0*U1*U2 + 8*U0^2*U3,
    U1^2*U2 - 4*U0*U2^2 + 2*U0*U1*U3 + 16*U0^2*U4,
    U1^2*U3 - 4*U0*U2*U3 + 8*U0*U1*U4,
    U0*U3^2 - U1^2*U4,
    U1*U3^2 - 4*U1*U2*U4 + 8*U0*U3*U4,
    U2*U3^2 - 4*U2^2*U4 + 2*U1*U3*U4 + 16*U0*U4^2,
    U3^3 - 4*U2*U3*U4 + 8*U1*U4^2
];

intrinsic BitangIdeal(f::RngMPolElt)->.
{given a homogeneous smooth plane quartic, return the ideal describing the
bitangents}
  R:=Parent(f);
  T<U,V,W>:=PolynomialRing(BaseRing(R),3, "grevlex");

  I:=ideal<Parent(U)|0>;
  for count in [1..6] do
    p0,p1:=Explode([<[0,W,-V],[V,-U,0]>,<[0,W,-V],[W,0,-U]>,
                   <[W,0,-U],[0,W,-V]>,<[W,0,-U],[V,-U,0]>,
                   <[V,-U,0],[0,W,-V]>,<[V,-U,0],[W,0,-U]>][count]);
    _<t>:=PolynomialRing(Parent(U));

    pt:=Vector(Parent(t),p0)+t*Vector(Parent(t),p1);
    cfs:=Eltseq(Evaluate(f,Eltseq(pt)));
    cfs:=cfs cat [0:i in [#cfs+1..5]];

    I:=I+ideal<Parent(U)|[Evaluate(l,cfs):l in BitangRelations]>;
  end for;
  return I,T;
end intrinsic;

intrinsic Discrim(F::RngMPolElt)-> .
{}
  R:=Parent(F);
  mons:=MonomialsOfDegree(R,5);
  x:=R.1;y:=R.2;z:=R.3;
  f:=[Derivative(F,i): i in [1..3]];
  J:=Determinant(Matrix([[Derivative(fi,j): j in [1..3]]:fi in f]));
  D:=[Derivative(J,i): i in [1..3]] cat [m*fi: m in [x^2,y^2,z^2,y*z,z*x,x*y], fi in f];
  return Determinant(Matrix([[MonomialCoefficient(d,m): m in mons]: d in D]))/2^17/3^9;
end intrinsic;

/******
Gamma:=sub<Sym(28)|(1, 2)(4, 5)(8, 21)(10, 13)(11, 25)(14, 17)(16, 20)(19, 22)(24, 26)(27, 28), (1, 3, 11)(2, 9, 21, 4, 12, 25)(5, 15, 19, 23, 26, 28)(6, 24, 27, 13, 16, 17)(7, 8, 10, 14, 18, 22)>;
QuadrupleOrbits:=Orbits(Gamma,GSet(Gamma,Subsets({1..28},4)));
SyzygeticQuadruples:=[o: o in QuadrupleOrbits | #o eq 315];
assert #SyzygeticQuadruples eq 1;
SyzygeticQuadruples:=SyzygeticQuadruples[1];

function SyzTriple(v)
    return exists{s: s in SyzygeticQuadruples | v subset s};
end function;
i3:=[i3: i3 in [3..28] | forall{v: v in Subsets({1,2,i3},3)| not(SyzTriple(v))}][1];
i4:=[i4: i4 in [3..28] | not(i4 in {1,2,i3}) and forall{v: v in Subsets({1,2,i3,i4},3)| not(SyzTriple(v))}][1];
i5:=[i5: i5 in [3..28] | not(i5 in {1,2,i3,i4}) and forall{v: v in Subsets({1,2,i3,i4,i5},3)| not(SyzTriple(v))}][1];
i6:=[i6: i6 in [3..28] | not(i6 in {1,2,i3,i4,i5}) and forall{v: v in Subsets({1,2,i3,i4,i5,i6},3)| not(SyzTriple(v))}][1];
function label(j)
    return [SyzTriple({1,i,j}) select 0 else 1: i in [2,i3,i4,i5,i6]];
end function;
******/

ZZ:=Integers();

function NormalizeForm(f)
    C:=Coefficients(f);
    return f div (GCD(C)*Sign(C[1]));
end function;

BitangentLabels:=[
    [],
    [],
    [],
    [],
    [],
    [],
    [ 1, 1, 1, 1, 1 ],
    [ 0, 0, 1, 1, 1 ],
    [ 1, 0, 1, 1, 0 ],
    [ 1, 1, 0, 1, 0 ],
    [ 0, 0, 0, 1, 0 ],
    [ 1, 0, 1, 1, 1 ],
    [ 1, 1, 1, 0, 0 ],
    [ 1, 1, 1, 0, 1 ],
    [ 1, 1, 0, 0, 1 ],
    [ 1, 0, 0, 1, 1 ],
    [ 1, 1, 0, 1, 1 ],
    [ 1, 0, 0, 0, 0 ],
    [ 0, 0, 0, 0, 0 ],
    [ 1, 0, 1, 0, 1 ],
    [ 0, 1, 0, 0, 0 ],
    [ 0, 1, 1, 1, 1 ],
    [ 1, 1, 1, 1, 0 ],
    [ 0, 0, 1, 0, 0 ],
    [ 0, 1, 0, 1, 1 ],
    [ 0, 1, 1, 0, 1 ],
    [ 0, 1, 1, 1, 0 ],
    [ 0, 0, 0, 0, 1 ]
];

intrinsic OrderedBitangents(F::RngMPolElt, B::SeqEnum) -> SeqEnum
{}
    R := Parent(F);
    assert BaseRing(R) eq ZZ and Rank(R) eq 3 and Degree(F) eq 4 and #B eq 6;
    X,Y,Z := Explode(OrderedGenerators(R));
    P2<x,y,z> := ProjectiveSpace(Rationals(),2);
    btcoords := [Eltseq(p) : p in Points(Scheme(P2,Basis(BitangIdeal(Evaluate(F,[x,y,z])))))];
    bitangents := [ NormalizeForm(w[1]*X+w[2]*Y+w[3]*Z) where
                        w:=ChangeRing(LCM([Denominator(a): a in p])*Vector(p),ZZ) : p in btcoords];
    Bref := [NormalizeForm(g) : g in B];
    bitangents := Bref cat [b : b in bitangents | b notin Bref];
    Discf := ZZ!Discrim(F);
    p := 10000;
    repeat
        p := NextPrime(p);
    until Discf mod p ne 0;
    Fq := GF(p^2);
    P2<xp,yp,zp> := ProjectiveSpace(Fq, 2);
    mons := MonomialsOfDegree(Parent(xp), 2);
    Cp := Curve(P2, Evaluate(F, [xp,yp,zp]));
// Edits tried here
    contact_points := [*[Matrix([[ Evaluate(m,q) : m in mons] where q := Eltseq(a): a in Support(Scheme(Cp,l))])]: l in bitangents*];
    // print contact_points;
    function IsSyz(v)
    // Edits tried here
        a := VerticalJoin(contact_points[v[1]]);
        b := VerticalJoin(contact_points[v[2]]);
        c := VerticalJoin(contact_points[v[3]]);
        d := VerticalJoin(a,b);
        if #Rows(VerticalJoin(d,c)) eq 6 then
            if Determinant(VerticalJoin(d,c)) eq 0 then
                return 0;
            else
                return 1;
            end if;
        else print "Hyperflex";
             return 2;
        end if;
    end function;
    function label(j)
        seq := [2,2,2,2,2];
        for i in [2..6] do
            if IsSyz([1,i,j]) eq 2 then
                break;
            else seq[i-1]:= IsSyz([1,i,j]);
            end if;
         end for;
        return seq;
       // return [IsSyz([1,i,j]) : i in [2..6]];
    end function;
    Result:=bitangents[1..6];
    for i in [7..28] do
         // print i;
         // print label(i);
        if 2 in label(i) then
            Result := bitangents[1..28] cat bitangents[1..2];
            return Result;
        else
        j := Index(BitangentLabels, label(i));
        Result[j] := bitangents[i];
        end if;
    end for;
    return Result;
end intrinsic;

RR<a0,a1,a2,a3,a4,a5,c,d>:=PolynomialRing(Rationals(),8,"grevlex");
RRX<xr,yr,zr>:=PolynomialRing(RR,3);

intrinsic Dvalue(F::RngMPolElt, Syz::SeqEnum)->.
{}
    J:=Ideal(Coefficients(&*[Evaluate(l,[xr,yr,zr]): l in Syz]+
        c*Evaluate(F,[xr,yr,zr])-d*(a0*xr^2+a1*yr^2+a2*zr^2+a3*xr*yr+a4*xr*zr+a5*yr*zr)^2));
    for v in [a0,a1,a2,a3,a4,a5] do
        soln:=Variety(J+ideal<RR|v-1>);
        if #soln eq 1 then
            dval:=soln[1][8];
            return SquareFree(Numerator(dval)*Denominator(dval));
        elif #soln gt 1 then
            error "Invalid solution";
        end if;
    end for;
    error "Not a syzygetic quadruple";
end intrinsic;

SyzygeticQuadruples:=[{4,7,10,23},{5,7,13,23},{4,6,25,27},{2,5,14,22},{5,6,14,23},{5,6,11,28},{1,4,17,19},{4,6,17,23},{1,5,15,24},{3,7,16,17},{3,6,12,23},{5,7,15,17},{2,4,15,26},{3,7,14,20},{4,7,14,15},{6,7,10,17},{2,5,11,18},{1,5,20,21},{4,6,9,16},{1,6,10,24},{1,2,27,28},{2,6,18,28},{5,6,9,20},{6,7,13,14},{2,5,13,27},{5,7,11,19},{1,6,11,13},{1,4,18,25},{2,4,8,16},{3,4,15,20},{2,4,18,24},{2,6,13,26},{3,5,9,13},{4,7,19,24},{1,6,18,27},{3,6,13,20},{1,5,13,28},{1,4,10,28},{4,7,22,25},{2,7,14,26},{2,6,10,25},{1,3,16,24},{2,3,12,22},{3,7,19,21},{3,5,15,16},{4,6,24,28},{5,7,12,20},{2,4,17,22},{1,5,18,26},{3,4,9,10},{5,7,22,26},{3,6,10,16},{2,4,10,27},{3,5,12,14},{2,7,8,12},{1,7,17,24},{2,3,20,26},{1,3,12,19},{3,7,8,22},{1,7,18,22},{5,6,26,27},{4,7,12,16},{1,5,14,19},{6,7,9,12},{6,7,19,28},{2,5,8,20},{3,4,12,17},{1,7,12,21},{3,6,8,27},{1,2,8,21},{1,6,19,23},{2,7,17,25},{2,6,22,23},{2,7,18,19},{4,6,13,15},{4,5,25,26},{5,6,10,15},{6,7,22,27},{1,4,16,21},{1,2,19,22},{3,4,8,25},{3,6,21,28},{4,5,16,20},{1,2,11,26},{1,7,11,14},{2,6,8,9},{4,5,11,24},{1,2,24,25},{3,7,9,23},{3,5,11,21},{1,3,9,28},{1,3,8,18},{1,6,9,21},{2,5,15,25},{1,7,23,28},{4,5,14,17},{2,3,9,27},{1,4,11,15},{2,3,18,21},{3,4,21,24},{4,5,10,13},{2,7,23,27},{3,5,8,26},{2,3,16,25},{1,3,11,20},{7,9,15,18},{4,19,20,27},{2,12,13,24},{1,13,16,22},{5,16,22,28},{7,13,16,18},{1,10,12,26},{2,10,19,20},{7,10,18,20},{6,12,24,26},{3,15,19,27},{3,14,25,28},{2,13,17,21},{6,8,11,17},{6,8,15,19},{2,17,20,28},{3,15,22,28},{3,11,17,27},{1,8,10,14},{6,14,21,25},{6,15,21,22},{1,17,20,27},{1,14,16,27},{4,18,20,23},{6,8,14,24},{5,21,23,25},{1,16,23,26},{1,9,15,22},{3,10,14,18},{6,17,21,26},{4,20,22,28},{1,10,20,22},{3,14,24,27},{5,9,22,24},{2,14,16,28},{3,13,17,18},{5,16,18,23},{7,13,21,25},{4,8,11,23},{1,8,15,23},{2,20,23,24},{3,17,26,28},{2,9,15,19},{5,16,19,27},{2,13,16,19},{7,16,26,28},{3,13,22,24},{4,9,19,26},{7,15,21,27},{5,9,17,18},{6,11,16,22},{7,20,25,28},{7,8,10,11},{2,15,21,23},{3,10,19,26},{2,9,14,24},{7,9,11,25},{1,20,23,25},{5,12,24,27},{5,17,21,27},{7,8,15,28},{7,20,24,27},{5,8,17,28},{7,11,16,27},{4,8,13,19},{4,9,14,18},{6,19,20,25},{5,10,21,22},{1,9,17,26},{3,11,23,25},{4,21,23,26},{2,11,16,23},{4,12,26,28},{6,16,19,26},{3,15,18,23},{4,8,14,28},{5,8,10,19},{4,14,21,27},{1,8,13,17},{5,8,23,24},{6,11,12,25},{2,10,14,21},{4,13,21,22},{7,10,21,26},{3,23,24,26},{7,9,24,26},{5,12,25,28},{6,20,22,24},{5,10,12,18},{2,12,15,28},{4,12,13,18},{7,8,13,24},{2,10,11,12},{4,11,12,27},{1,12,15,27},{5,9,19,25},{1,12,13,25},{1,9,14,25},{6,14,16,18},{3,10,11,22},{3,13,19,25},{4,9,11,22},{6,12,15,18},{6,17,18,20},{2,9,11,17},{8,19,21,22},{8,12,14,26},{8,15,16,26},{12,17,21,24},{10,18,25,28},{15,20,21,24},{10,17,19,28},{11,13,18,27},{13,14,22,27},{12,13,20,23},{15,18,24,26},{9,16,25,27},{10,12,16,23},{16,20,25,26},{8,16,17,22},{19,22,27,28},{9,11,20,28},{9,14,20,23},{11,24,25,26},{14,17,25,26},{11,16,20,24},{8,14,20,22},{14,19,20,21},{24,25,27,28},{9,12,19,28},{11,13,19,23},{9,16,17,23},{18,20,21,26},{8,11,18,20},{8,12,18,19},{10,19,23,24},{11,14,17,24},{16,17,19,21},{11,26,27,28},{9,12,22,27},{10,22,23,25},{8,16,18,24},{16,18,21,25},{12,18,21,22},{13,22,23,26},{14,23,26,27},{12,20,22,26},{10,18,24,27},{9,13,15,16},{9,10,12,17},{11,12,19,20},{11,14,18,22},{10,17,22,27},{9,16,24,28},{11,15,16,21},{8,12,23,27},{17,23,24,28},{13,18,26,28},{15,17,22,26},{12,16,19,24},{9,10,15,20},{8,9,18,28},{9,20,26,27},{9,19,21,23},{9,12,13,14},{11,15,17,19},{12,16,22,25},{17,18,19,25},{13,14,19,28},{13,15,17,23},{8,15,20,25},{11,12,14,21},{12,21,23,28},{10,13,25,26},{14,15,19,24},{17,23,25,27},{11,15,18,25},{8,9,10,25},{11,14,23,28},{9,18,21,27},{13,20,21,28},{8,9,22,23},{14,15,22,25},{13,15,24,28},{13,15,25,27},{10,14,15,23},{8,12,17,25},{8,21,24,25},{10,11,13,24},{8,13,20,27},{18,19,23,27},{9,11,13,21},{8,10,16,27},{10,15,26,27},{10,11,15,28},{14,18,19,26},{11,19,22,26},{8,11,21,26},{10,16,21,28},{10,13,16,20},{18,22,23,28},{10,13,14,17},{12,15,17,20},{9,10,21,24},{8,21,27,28},{17,18,22,24},{19,22,24,25},{14,16,17,20},{12,14,15,16},{8,9,13,26}];

btrformat:=recformat<f: RngMPolElt, disc: RngIntElt, bitangs: SeqEnum, S: SeqEnum, H1S: ModTupFld, UsefulTriples: SeqEnum>;

intrinsic InitBitangs(F::RngMPolElt,BTref::SeqEnum)-> Rec
{}
    disc:=ZZ!Discrim(F);
    S:=[-1] cat PrimeDivisors(disc);
    H1S:=VectorSpace(GF(2),6*#S);
    bitangents:=OrderedBitangents(F,BTref);
    if #bitangents eq 28 then
        Ds:=[Dvalue(F,bitangents[Setseq(s)]): s in SyzygeticQuadruples[1..210]];
        UsefulTriples:=[[]: i in [1..7]];
        for i in [1..210] do
            s:=SyzygeticQuadruples[i];
            for j in [1..7] do
                if j in s then
                    Append(~UsefulTriples[j],<Setseq(Exclude(s,j)),Ds[i]>);
                end if;
            end for;
        end for;
        return rec<btrformat|f:=F, disc:=disc, bitangs:=bitangents, S:=S, H1S:=H1S, UsefulTriples:=UsefulTriples>;
   else return rec<btrformat|f:=F, disc:=disc, bitangs:=bitangents[1..28], S:=S, H1S:=H1S, UsefulTriples:=[]>;
   end if;
end intrinsic;

intrinsic LocalPoints(btr::Rec,p::RngIntElt,working_precision::RngIntElt)->SeqEnum
{}
    f:=btr`f;
    Zp:=pAdicRing(p:Precision:=working_precision);
    Rp<xp,yp>:=PolynomialRing(Zp,2);
    Fp:=ResidueClassField(Zp);
    A2k<xkp,ykp>:=AffineSpace(Fp,2);
    procedure rec(fp,x0,y0,e,~Points)
       fk:=Evaluate(fp,[xkp,ykp]);
       gradfk:=[Derivative(fk,i): i in [1,2]];
       for P in RationalPoints(Scheme(A2k,fk)) do
           Ps:=Eltseq(P);
           x1:=ZZ!Ps[1];
           y1:=ZZ!Ps[2];
           if exists{g: g in gradfk | Evaluate(g,Ps) ne 0} then
               Append(~Points,[elt<Zp|0,x0+p^e*x1,e+1>,elt<Zp|0,y0+p^e*y1,e+1>]);
           else
               g:=Evaluate(fp,[x1+p*xp,y1+p*yp]);
               rec(g div Content(g),x0+p^e*x1,y0+p^e*y1,e+1,~Points);
           end if;
       end for;
    end procedure;

    fp:=Evaluate(f,[xp,yp,1]);
    fp:=fp div Content(fp);
    P1:=[];
    rec(fp,0,0,0,~P1);
    Points:=[[pt[1],pt[2],1]:pt in P1];
    
    fp:=Evaluate(f,[xp,1,p*yp]);
    fp:=fp div Content(fp);
    P1:=[];
    rec(fp,0,0,0,~P1);
    Points cat:= [[pt[1],1,p*pt[2]]:pt in P1];

    fp:=Evaluate(f,[1,p*xp,p*yp]);
    fp:=fp div Content(fp);
    P1:=[];
    rec(fp,0,0,0,~P1);
    Points cat:= [[1,p*pt[1],p*pt[2]]:pt in P1];

    return Points;
end intrinsic;

intrinsic LocalImage(btr::Rec,Points::SeqEnum)->SetEnum, Map
{}
    bitangents:=btr`bitangs;
    UsefulTriples:=btr`UsefulTriples;
    Zp:=Universe(Points[1]);
    p:=Prime(Zp);

    Qp:=FieldOfFractions(Zp);
    SQp,toSQp:=pSelmerGroup(2,Qp);
    H1p:=VectorSpace(GF(2),6*#Invariants(SQp));
    
// The next lines are new - want algorithm to check if Selmer set is empty, and if so conclude that there aren't rational pts 
// print SQp;
// if #SQp = 0 then
//    return "Selmer set is empty, so there are no rational points";
// end if;

    V:=[];
    for P in Points do
        btP:=[Evaluate(b,P):b in bitangents];
        v4:=Valuation(Zp!4);
        usable:=[RelativePrecision(a) gt v4: a in btP];
        function select_value(U)
            if exists(u0){u: u in U |&and usable[u[1]]} then
                return u0[2]*&*btP[u0[1]];
            else
                return 0;
            end if;
        end function;
        w:=[toSQp(select_value(U)):U in UsefulTriples];
        Append(~V,H1p!&cat[Eltseq(w[i]+w[7]): i in [1..6]]);
    end for;
    A:=Matrix(GF(2),[Eltseq(toSQp(a)): a in btr`S]);
    H1StoH1p:=hom<btr`H1S->H1p| DiagonalJoin([A,A,A,A,A,A])>;
    return Seqset(V),H1StoH1p;
end intrinsic;

intrinsic twoSelmerMap(Zp::RngPad)-> Map
{}
    F2:=GF(2);
    if Prime(Zp) eq 2 then
        dict:=[[F2|0,0],[],[1,0],[],[0,1],[],[1,1]];
        function modsq2(a)
            if RelativePrecision(a) le 2 then
                error "Insufficient precision";
            end if;
            v:=Valuation(a);
            return [F2|v mod 2] cat dict[(ZZ!ShiftValuation(a,-v)) mod 8];
        end function;
        return modsq2;
    else
        function modsqp(a)
            if RelativePrecision(a) eq 0 then
                error "Insufficient precision";
            end if;
            v:=Valuation(a);
            return [F2|v mod 2,IsSquare(ShiftValuation(a,-v)) select 0 else 1];
        end function;
        return modsqp;
    end if;
end intrinsic;
            
intrinsic ComputeLocalImage(btr::Rec, p::RngIntElt, working_precision::RngIntElt) -> SetEnum, Map
{}
    f := btr`f;
    Zp := pAdicRing(p : Precision:=working_precision);
    v4 := Valuation(Zp!4);
    Rp<xp,yp> := PolynomialRing(Zp, 2);
    Fp := ResidueClassField(Zp);
    A2k<xkp,ykp> := AffineSpace(Fp, 2);
    Pk:=[xkp,ykp];
    Rkp:=Parent(xkp);
    Bools:=Booleans();
    
    bitangents := btr`bitangs;
// Usually we want to take out these print statements.
//    print "bitangents", bitangents;
    UsefulTriples := btr`UsefulTriples;
//    print "UsefulTriples", UsefulTriples;
    toSQp := twoSelmerMap(Zp);
    H1p := VectorSpace(GF(2), p eq 2 select 18 else 12);
    A := Matrix(GF(2), [toSQp(Zp!a) : a in btr`S]);
//DELETE or comment out following print statement    
//    print DiagonalJoin([A,A,A,A,A,A]);
    H1StoH1p := hom< btr`H1S->H1p | DiagonalJoin([A,A,A,A,A,A]) >;
    
/* The next lines are new - want algorithm to check if selmer set is empty, and if so conclude that there aren't rational pts 
    Qp := FieldOfFractions(Zp);
    SQp := pSelmerGroup(2, Qp);
    print "The Selmer set is a f.g. abelian group of order", #SQp;
    if #SQp eq 0 then
        return "Selmer set is empty, so there are no rational points";
    end if;
*/
    Result:={};
    
    for Paff in [[xp,yp,1],[xp,1,p*yp],[1,p*xp,p*yp]] do
        fp := Evaluate(f, Paff);
        fp := fp div Content(fp);
        bitangents_affine := [Evaluate(b, Paff) :b in bitangents];
       //  print "Patch", Paff;
     
        procedure rec(fp, x0, y0, e, ~Result)
            fk := Evaluate(fp, Pk);
            gradfk := [ Derivative(fk, 1), Derivative(fk, 2) ];  
            for P in RationalPoints(Scheme(A2k, fk)) do
                Ps := Eltseq(P);
                x1 := ZZ!Ps[1];
                y1 := ZZ!Ps[2];
                x0new := x0+p^e*x1;
                y0new := y0+p^e*y1;
                if exists{g : g in gradfk | Evaluate(g, Ps) ne 0} then
                    Paff := [Zp|elt<Zp | 0, x0new, e+1>, elt<Zp | 0, y0new, e+1>];
                    btP := [ Evaluate(b, Paff) : b in bitangents_affine[1..7]];
                    usable := [ RelativePrecision(a) gt v4 : a in btP ];
                    if &and(usable) then
                        w := [ toSQp(v) : v in btP ];
                        Include(~Result, H1p!(&cat(w[1..6])) + H1p!(&cat[w[7],w[7],w[7],w[7],w[7],w[7]]) );
                        continue; //we've found an image so we do NOT recurse on this point
                    end if;

                    btP2 := [ Evaluate(b, Paff) : b in bitangents_affine[8..28] ];
                    usable cat:= [ RelativePrecision(a) gt v4 : a in btP2 ];
                    btP cat:= btP2;

                    function select_value(U)
                        if exists(u0){ u : u in U | &and(usable[u[1]]) } then
// Ammended next line
                 //           print u0;
                            return u0[2] * &*btP[u0[1]];
                        else
                            return 0;
                        end if;
                    end function;

                    w := [];
                    flag:=true;
                    for i in [1..7] do
               // Ammended
               //     print <Paff,i,usable[i]>;
                        if usable[i] then
                            w[i]:=toSQp(btP[i]);
                        else
                            v:= select_value(UsefulTriples[i]);
               // Ammended
               //             print v;
                            if v eq 0 then
                                flag:=false;
                                break;
                            else
                                w[i]:=toSQp(v);
                            end if;
                        end if;
                    end for;

                    if flag then
                        Include(~Result, H1p!(&cat(w[1..6])) + H1p!(&cat[w[7],w[7],w[7],w[7],w[7],w[7]]) );
                        continue; //we've found an image so we do NOT recurse on this point
                    else
                        print "We're lifting further!";
                    end if;
                end if;
                //at this point, either the point wasn't coming from a nonsingular
                //point in reduction or we didn't have enough precision to determine the value
                //of the bitangents. So we recurse on it.
                g := Evaluate(fp, [Rp|x1+p*xp, y1+p*yp]);
                rec(g div Content(g), x0new, y0new, e+1, ~Result);
           end for;
        end procedure;

        rec(fp, 0, 0, 0, ~Result);
    end for;

    return Result, H1StoH1p;
end intrinsic;

intrinsic RealCase(btr::Rec) -> SeqEnum, SetEnum, ModTupFld, Map
{Computes contact points of f with lines joining extremal values (over RR), returns contact points and local image W}
    f := btr`f;
    A2<x,y>:=PolynomialRing(Rationals(),2);
    F:=Evaluate(f,[x,y,1]);
    dFx:=Derivative(F,x);
    dFy:=Derivative(F,y);
    G:=Resultant(dFx,dFy,1);

    RR:=RealField(200);
    RRT<T>:=PolynomialRing(RR);
    RRXYZ<XX,YY,ZZ>:=PolynomialRing(RR,3);
    yvals:=Roots(Evaluate(G,[0,T]));
    Points:=[];
    for yv in yvals do
        xv1:=[x[1]: x in Roots(Evaluate(dFx,[T,yv[1]]))];
        xv2:=[x[1]: x in Roots(Evaluate(dFy,[T,yv[1]]))];
        for x0 in xv1 do
             matches:=[x1: x1 in xv2 | Abs(x0-x1) lt 10^(-150)];
             if #matches gt 1 then
                 error "Ambiguous";
             end if;
             if #matches eq 1 then
                 Append(~Points,[x0,yv[1],1]);
             end if;
        end for;
    end for;

    // "Only combine points with others of opposite sign".
    ptsgn:=[Sign(Evaluate(f,Points[i])): i in [1..#Points]];
    
    // We compute the contact points of f with the parameterised lines, and test
    CPoints:= [];
    for i in [1..#Points] do
        for j in [1..#Points] do
            if ptsgn[i] * ptsgn[j] eq -1 then
                    m := (Points[i,2]-Points[j,2])/(Points[i,1]-Points[j,1]);
                    l := YY - m*(XX - Points[j,1]) - Points[j,2]*ZZ;
                    param := [(Points[i,1]-Points[j,1])*T + Points[j,1],(Points[i,2]-Points[j,2])*T + Points[j,2],1];
                    if Abs(Evaluate(Evaluate(l,param),1)) gt 10^(-150) then
                        error "The line has not been properly parameterised.";
                    end if;
                    fpoly:=Evaluate(f,param);
                    froots:=[r[1]: r in Roots(fpoly)];
                    CPoints cat:=[[Evaluate(p,rt): p in param]:rt in froots];
            end if;
        end for;
    end for;
    // Should see all true if not commented out 
    // [Abs(Evaluate(f,p)) lt 10^(-100): p in CPoints];
    
    W := {Vector([m[i]+m[7]: i in [1..6]]) where m:=[GF(2)|(1-Sign(Evaluate(b, p))) div 2: b in btr`bitangs[1..7]]: p in CPoints};
    Wsub, map := sub<VectorSpace(GF(2),6)|[w-w0: w in W]> where w0:=Rep(W);
    H1v := Codomain(map);
    s := #btr`S;
    length := 36*s;
    Seq := [0^^length];
    for i in [1..6] do
        Seq[(6*s+1)*i-6*s] := 1;
    end for;
    A := Matrix(GF(2),6*s,6,Seq);
    map2 := hom< btr`H1S->H1v |A>;
    
    return CPoints, Wsub, map2;
end intrinsic