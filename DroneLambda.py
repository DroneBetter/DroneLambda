from functools import reduce
from itertools import chain,pairwise,starmap
from copy import deepcopy
from math import gcd,log
from fractions import Fraction
from numbers import Number
dbg=(lambda x,*s: (x,print(*s,x))[0]) #debug
revange=(lambda a,b=None,c=1: range(b-c,a-c,-c) if b else range(a-c,-c,-c))
decompose=(lambda n,l=None: (n>>i&1 for i in range(n.bit_length() if l==None else l)) if isinstance(n,Number) else chain(*n))
recompose=(lambda i: reduce(int.__or__,(k<<j for j,k in enumerate(i))))

digits='0123456789'
#indexes=       (  0,      1,      2,      3,   4,       5,  6,       7,  8,  9,  10,         11,       12)
prec=           (('|',), ('^',), ('&',), ('<<','>>'),  ('+','-'),   ('*','/','%','//'),      ('~',),  ('**',), ('log',))
commutativities=((True,),(True,),(True,),(False,False),(True,False),(True,False,False,False),(False,),(False,),(False,)) #with themselves
associativities=((True,),(True,),(True,),(False,False),(True,False),(True,False,False,False),(False,),(False,),(False,))
rights=         ( False,  False,  False,  False,        False,       False,                   False,   True,    False)
(ops,unc,una)=map(lambda p: tuple(decompose(p)),(prec,commutativities,associativities))
precs=tuple(map(lambda o: next(filter(lambda p: o in p[1],enumerate(prec)))[0],ops))
assocpairs=     (  (),     (),     (),     (),  (),     (6,),(5,),   (8,),(7,),(),(),          (),      (),     ())
assocpairs=tuple(starmap(lambda i,a: (i,)*a[0]+a[1],enumerate(zip(una,assocpairs))))
unaries=(6,8)

strucget=(lambda struc,inds: reduce(lambda a,b: a[b],inds[:-1],struc))
def structrans(struc,f=None,lf=None,rev=False,fints=False):
    inds=[len(struc)-1 if rev else 0]
    b=False
    while len(inds) and type(struc)==list and 0<=inds[0]<len(struc):
        if f:
            (struc,inds)=f(struc,inds)
        if type(strucget(struc,inds))==list:
            if lf:
                (struc,inds)=lf(struc,inds)
            inds.append(len(strucget(struc,inds+[0]))-1 if rev and type(strucget(struc,inds+[0]))==list else 0)
        else:
            del inds[-1]
            if len(inds):
                inds[-1]+=(-1)**rev
        while len(inds) and (isinstance(strucget(struc,inds),Number) or (inds[-1]<0 if rev else len(strucget(struc,inds))<=inds[-1])):
            if f and fints and isinstance(strucget(struc,inds),Number):
                (struc,inds)=f(struc,inds)
            del inds[-1]
            if not inds:
                b=True
                break
            inds[-1]+=(-1)**rev
        if len(inds) and b: break
    if f and (type(struc)==list or fints):
        struc=f(struc,[0])[0]
    if lf and type(struc)==list:
        struc=lf(struc,[0])[0]
    return(struc)

def strucset(struc,inds,val): #function call cannot be assigned to directly for whatever reason
    if len(inds)>1:
        strucget(struc,inds[:-1])[inds[-2]]=val
    else:
        struc=val
    return(struc)

def strucsert(struc,inds,nind,val): #function call cannot be assigned to directly for whatever reason
    s=strucget(struc,inds)
    s.insert(nind,val)
    return(strucset(struc,inds,s))

def lisp(struc,inds,p,o,rev=False): #my beloved
    g=strucget(struc,inds)
    if strucget(struc,inds) in o:
        if not p: #precedence 0, word function (ie. log)
            f=strucget(struc,inds)
            del strucget(struc,inds[:-1])[inds[-2]]
            strucsert(struc,inds,0,f)
            inds.append(0)
        elif strucget(struc,inds)=='~':
            operands=strucget(struc,inds[:-1])[inds[-2]:inds[-2]+2]
            del strucget(struc,inds[:-1])[inds[-2]:inds[-2]+2]
            del inds[-1]
            strucsert(struc,inds,inds[-1],operands)
            inds.append(1)
        elif not rev or inds[-2]>0:
            sub=(strucget(struc,inds) in {'-','/'}) #subtraction and division to unaries
            operands=(lambda a,f,b: (['*',a,['/',b]] if strucget(struc,inds)=='/' else ['+',a,['-',b]]) if sub else [f,a,b])(*strucget(struc,inds[:-1])[inds[-2]-1:inds[-2]+2])
            del strucget(struc,inds[:-1])[inds[-2]-1:inds[-2]+2]
            del inds[-1]
            strucsert(struc,inds,inds[-1]-1,operands)
            inds[-1]-=1
            inds.append(2)
            if sub:
                inds.append(1)
    return(struc,inds)

def unbracket(struc,inds): #not closed-form because in-place
    if len(strucget(struc,inds))==1:
        struc=strucset(struc,inds,strucget(struc,inds)[0])
        del inds[-1]
    return(struc,inds)

straction=(lambda n: "Fraction("+str(n.numerator)+","+str(n.denominator)+")" if type(n)==Fraction else str(n)) #very suspicious
def enact(struc,inds):
    global diff
    e=strucget(struc,inds)
    if type(e)==list:
        if e[0]=='-':
            if isinstance(e[1],Number):
                diff=True
                struc=strucset(struc,inds,-e[1])
        elif e[0] in ops and e[0]!='/':
            if all(map(lambda x: isinstance(x,Number),e[1:])):
                diff=True
                struc=strucset(struc,inds,eval(straction(e[1])+e[0]+straction(e[2])))
    elif type(e)==Fraction and e.denominator==1:
        diff=True
        struc=strucset(struc,inds,e.numerator)
    return(struc,inds)

def inter(struc,inds):
    if type(strucget(struc,inds))!=list:
        struc=strucset(struc,inds,1)
    return(struc,inds)

def collapse(struc,inds):
    global diff
    if all(map(lambda x: isinstance(x,Number),strucget(struc,inds))):
        diff=True
        struc=strucset(struc,inds,sum(strucget(struc,inds)))
    return(struc,inds)

def stringer(struc,inds):
    g=strucget(struc,inds)
    if tuple!=type(g)!=list and g not in ops: #will have to be changed if functions are to be passed around within expressions (as I have been known to do)
        struc=strucset(struc,inds,(str(g),-1,0)) #it is a little-known fact that -1 is infinite (if you look at its binary representation), factorial agrees :-)
    return(struc,inds)

def strapse(struc,inds):
    brack=(lambda t,g,i: '('+t[0]+')' if (0<=t[1]<g or t[1]==g and not una[i]) and t[2] not in assocpairs[i] else t[0])
    global diff
    g=strucget(struc,inds)
    f=g[0]
    if type(g)==list and all(map(lambda x: type(x)==tuple,g[1:])): #tuples here used for storing precedence (very suspicious)
        i=ops.index(f)
        p=precs[i]
        diff=True
        struc=strucset(struc,inds,(f+'('+','.join(map(lambda g: str(g[0]),g[1:]))+')' if p==len(prec)-1 else f+brack(g[1],p,i) if len(g)==2 else brack(g[1],p,i)+f+brack(g[2],p,i),p,i))
    return(struc,inds)

def enmax(struc,f,i=None,fints=False,iints=False):
    muc=deepcopy(struc)
    if i:
        muc=structrans(muc,i,fints=iints)
    #print(struc)
    global diff
    diff=True
    while diff:
        diff=False
        muc=structrans(muc,f,fints=fints)
    return(muc)

cost=(lambda struc: enmax(struc,collapse,inter,False,True))
compute=(lambda struc: enmax(struc,enact,fints=True))
strucstr=(lambda struc: enmax(struc,strapse,stringer,False,True)[0])

inp=(input(''))#dbg("(x+y+z)*(x**2+y**2+z**2-x*y-y*z-z*x)")#"(a+b)*(a+b)+0"#"((3+4-x+22-3)/3*(2+5-y+4-7)*5**4**2"
if type(inp)==str:
    if '[' in inp: #they are not currently used for anything
        struc=eval(inp)
    else:
        inp=inp.replace(' ','')
        struc=[]
        acc=''
        for i in inp:
            if i in ('(',')')+ops:
                struc+=[acc]*bool(acc)+[i]
                acc=''
            else:
                acc+=i
        if acc:
            struc.append(acc)
        struc=list(map(lambda n: int(n) if all(map(digits.__contains__,n)) else n,struc)) #recognise ints
        s=0
        while s<len(struc):
            if struc[s]=='-' and isinstance(struc[s+1],Number):
                if s==0 or struc[s-1]=='(':
                    del struc[s]
                    struc[s]*=-1
                else:
                    struc[s]='+'
                    struc[s+1]*=-1
            else:
                s+=1

        new=[]
        no=False
        for a,b in pairwise(struc):
            if no:
                no=False
            else:
                if a==b and (a=='*' or a=='/'):
                    new.append(2*a)
                    no=True
                else:
                    new.append(a)
        new.append(struc[-1])
        openings=[]
        closings=[]
        bracks=[]
        for i,n in enumerate(new):
            b=(1 if n=='(' else -1 if n==')' else 0)
            if b:
                (openings if b==1 else closings).append(i)
            bracks.append((bracks[-1] if bracks else 0)+b)

        left=right=m=abs(min(bracks))
        if len(openings)!=len(closings) or left:
            disp=abs(len(openings)-len(closings))
            if len(openings)>len(closings):
                right+=disp
            else:
                left+=disp
            if bracks[-1]<0:
                m+=bracks[-1]
            if left>m<right:
                m=min(left,right)-m
                left-=m
                right-=m
            openings=list(range(left))+[o+left for o in openings]
            new=['(']*left+new
            closings=[c+left for c in closings]+list(range(len(new),len(new)+right))
            new+=[')']*right
            bracks=list(range(1,left+1))+[b+left for b in bracks]+list(revange(right))
            print("attempted to fix mismatched brackets")
            print(''.join(map(str,new)))

        struc=[]
        i=0
        inds=[0]
        while i<len(new):
            if i in openings:
                strucget(struc,inds).append([])
                inds.append(0)
            else:
                if i in closings:
                    del inds[-1]
                else:
                    strucget(struc,inds).append(new[i])
                inds[-1]+=1
            i+=1
        struc=structrans(reduce(lambda s,o: structrans(struc,lambda s,i: lisp(s,i,o[0],*o[1]),rev=o[1][1]),enumerate(zip(prec[::-1],rights[::-1])),structrans(struc,lf=unbracket)),lf=unbracket)
else:
    struc=inp

print(strucstr(struc))
struc=compute(struc)

def mutate(struc,inds): #objective simplifications override all others found prior, to speed it up
    transitions=[]
    def transpend(trans,over):
        global manual
        nonlocal transitions,itsOver
        if over and not manual:
            transitions=trans
            itsOver=True
        else:
            transitions.append(trans)
        return(over)
    itsOver=False #others not generated if a reduction is found
    call=strucget(struc,inds)
    if type(call)==list:
        f=call[0]
        if f in ops:
            if f=='/' and call[1]==1:
                transpend(compute(strucset(deepcopy(struc),inds,1)),False) #inelegant but Python doesn't seem to allow nonlocal breaks
            else:
                for comm,call in (lambda c: ((0,c),(1,(lambda f,a,b: [f,b,a])(*c))) if unc[ops.index(c[0])] else ((0,c),))(call): #commutativity
                    if f=='+' and call[2]==0 or f in {'*','**'} and call[2]==1: #additive/multiplicative/divisive/exponential identities (can be removed without loss of generality)
                        if transpend(compute(strucset(deepcopy(struc),inds,call[1])),False): #inelegant but Python doesn't seem to allow nonlocal breaks
                            break
                    else:
                        if f=='*':
                            if type(call[1])==list and call[1][0]=='+': #distributivity ((a+b)*c=a*c+b*c)
                                transitions.append(compute(strucset(deepcopy(struc),inds,(lambda a,b: ['+',[f,a[1],b],[f,a[2],b]])(*call[1:]))))
                            elif isinstance(call[1],Number) and type(call[2])==list and call[2][0]=='/':
                                if transpend(strucset(deepcopy(struc),inds,Fraction(call[1],call[2][1])),False): #not any(map(lambda c: isinstance(c,Number),call[1:])) and gcd(*call[1:])!=1
                                    break
                        elif f=='+' and type(call[1])==list and call[1][0]=='*': #antidistributivity (a*c+b*c=(a+b)*c (capitalism))
                            if type(call[2])==list and call[2][0]=='*' and call[2][1]==call[1][1]: #all(map(lambda n: type(n)==list and n[0]=='*',call[1:])) and call[1][1]==call[2][1]: #hmm
                                if transpend(compute(strucset(deepcopy(struc),inds,(lambda f,a,b: ['*',a[1],['+',a[2],b[2]]])(*call))),False):
                                    break
                            elif call[1][1]==call[2]:
                                if transpend(compute(strucset(deepcopy(struc),inds,(lambda f,a,b: ['*',a[1],['+',a[2],1]])(*call))),False):
                                    break
                        if type(call[1])==list:
                            g=ops.index(call[1][0])
                            if g not in unaries and g in assocpairs[ops.index(f)]: #associativity (swapping precedence)
                                if transpend(compute(strucset(deepcopy(struc),inds,(lambda f,a,b: [a[0],[f,a[1],b],a[2]])(*call))),False):
                                    break
                    if comm:
                        transitions.append(compute(strucset(deepcopy(struc),inds,call)))
    elif type(call)==Fraction:
        transitions.append(compute(strucset(deepcopy(struc),inds,['*',call.numerator,['/',call.denominator]])))
    #print(tuple(map(lambda t: strucstr(t),transitions)))
    return(transitions,itsOver)

def mutations(struc): # #intended to be such that all(map(lambda t: i in mutations(t)[0],mutations(i)[0])) is True
    (transitions,itsOver)=mutate(deepcopy(struc),[0])
    if not itsOver:
        inds=[0]
        go=False
        b=False
        while type(struc)==list and inds[0]<len(struc):
            if type(strucget(struc,inds))==list:
                inds.append(0)
                if go:
                    (newTransitions,newOver)=mutate(deepcopy(struc),inds)
                    if newOver:
                        transitions=newTransitions
                        itsOver=True
                        break
                    else:
                        transitions+=newTransitions
                    go=False
            else:
                call=strucget(struc,inds)
                if type(call)==Fraction:
                    strew=deepcopy(struc)
                    transitions.append(compute(strucset(strew,inds,['*',call.numerator,['/',call.denominator]])))
                del inds[-1]
                inds[-1]+=1
            while isinstance(strucget(struc,inds),Number) or (inds[-1]>=len(strucget(struc,inds))):
                del inds[-1]
                if not inds:
                    b=True
                    break
                inds[-1]+=1
            go=True
            if b: break
    return(transitions,itsOver)


manual=False
if manual:
    while True:
        print(strucstr(struc))
        states=list(mutations(struc)[0])
        print('\n'.join(starmap(lambda i,s: str(i)+'. '+strucstr(s)+' ('+str(s)+')',enumerate(states))))
        while True:
            dec=input("which ")
            if all(map(digits.__contains__,dec)):
                dec=int(dec)
                if dec<len(states):
                    break
        struc=states[int(dec)]
else:
    print('mutating')
    states=[struc]
    stateTransitions=[[]]
    searcheds=[False]
    dist=1
    changed=True
    while dist<18 and changed:
        print(dist,len(states),*(lambda s: (cost(s),strucstr(s),s))(min(states,key=lambda s: cost(deepcopy(s)))))
        length=len(states)
        for i,(s,e) in enumerate(zip(states[:len(states)],searcheds[:len(states)])): #so that it doesn't continue searching states generated in this iteration
            if not e:
                (mut,over)=mutations(s)
                if over:
                    states=[mut]
                    stateTransitions=[[]]
                    searcheds=[False]
                    changed=True
                    break
                else:
                    for m in mut:
                        if m in states:
                            stateTransitions[i].append(states.index(m))
                        else:
                            changed=True
                            #print('n',len(states),m)
                            states.append(m)
                            searcheds.append(False)
                            stateTransitions.append([])
                            stateTransitions[i].append(len(states)-1)
        dist+=1
    #print('\n'.join(map(strucstr,states)))
