import copy
from collections import deque
import random

class Formula:
    def __init__(self, symbol, children, text):
        self.symbol = symbol #string
        self.children = children #lista de Formulas
        self.text = text #string
        
        self.variables = [] #lista de strings
    
    def __repr__(self):
        return self.text

    def updateText(self):
        self.text = self.toText()

    def toText(self): #mira el arbol y el simbolo y devuelve el texto que representa.
        if len(self.children) == 0:
            r = self.symbol
        else:
            r = self.symbol + '('
            for i in range(len(self.children) - 1):
                r += self.children[i].toText() + ','
            r += self.children[-1].toText() + ')'
        return r

    def toTree(self): #mira el texto y arma el árbol y el simbolo.
        self.children.clear()
        self.symbol = ''
        if len(self.text) > 0:
            i = 0
            while i < len(self.text) and self.text[i] != '(':
                i += 1
            if i == len(self.text):
                self.symbol = self.text
            else:
                self.symbol = self.text[:i] #o sea, ese texto pero solo los carecteres desde 0 hasta i-1 inclusives.
                while i < len(self.text) - 1:
                    m = i + 1
                    i = m
                    parenthesis = 0
                    goOn = True
                    while goOn:
                        i += 1
                        if self.text[i] == '(':
                            parenthesis += 1
                        elif self.text[i] == ')':
                            parenthesis -= 1

                        if parenthesis < 0:
                            goOn = False
                        elif parenthesis == 0 and self.text[i] == ',':
                            goOn = False
                    s = (self.text[m:])[:i-m]
                    self.children.append(Formula('', [], s))
                    self.children[-1].toTree()
    
    def contains(self, l): #le metes una hoja (leaf) l (por ejemplo, "a1", "p3", o "A1") en forma de texto y te dice si el arbol contiene a esa hoja. Asume que el texto es igual al arbol.
        return l == self.text or '('+l+')' in self.text or '('+l+',' in self.text or ','+l+',' in self.text or ','+l+')' in self.text #para que no flashee a1 en a17, ni b1 en ab1.
    
    def replace(self): #reemplaza todas las variables que sean key en extension por lo que hay en el ultimo elemento de esa lista de extension.
        self.replaceAux()
        self.updateText()
    
    def replaceAux(self):
            if self.symbol in extension:
                self.text = extension[self.symbol][-1].text
                self.toTree()
            else:
                for i in range(len(self.children)):
                    self.children[i].replaceAux()
    
    def listVariables(self, S): #le metés una lista de caracteres S y te devuelve la lista de todos los simbolos que aparecen en algún lugar del árbol que empiezan con caracter en S (y hace que self.variables sea esa lista). OJO: si sos medie salame y tenes una variable y un operador que empiezan con el mismo caracter (onda la variable '-a1' y el operador '->') puede flashear.
        self.variables = []
        if self.symbol[0] in S:
            self.variables.append(self.symbol)
        else:
            for ch in self.children:
                self.variables += ch.listVariables(S)
            self.variables = list(dict.fromkeys(self.variables)) #esto elimina las repetidas.
        return self.variables
                

class GraphNode:
    def __init__(self, name):
        self.name = name #string
        self.arrowsTo = [] # lista de GraphNode a los que apunta.
        self.arrowsFrom = [] # lista de GraphNode que apuntan a este.

class DGraph: #(grafo direccionado)
    def __init__(self, nodes): #nodes es un diccionario que las key son los name de los GraphNode y en ese lugar contiene a ese GraphNode.
        self.nodes = nodes
        self.isOrphan = {}
        self.findOrphans()
        self.buildArrowsFrom()

    def findOrphans(self): #arma el diccionario isOrphan, que le metés una key y te devuelve True o False según si ese nodo es o no (respectivamente) huérfano (llamamos nodo huérfano a uno que no tiene ninguno que apunte a él).
        self.isOrphan = {}
        for k in self.nodes:
            self.isOrphan[k] = True
        for k in self.nodes:
            for ar in self.nodes[k].arrowsTo:
                self.isOrphan[ar.name] = False
    
    def buildArrowsFrom(self): #arma arrowsFrom.
        for k in self.nodes:
            for ar in self.nodes[k].arrowsTo:
                self.nodes[ar.name].arrowsFrom.append(self.nodes[k])

    def hasLoops(self): #determina si en algún lado del grafo te podés loopear siguiendo la dirección de las flechas. Esta la programó Dylan.
        visited = set()
        ancestors_per_node = dict(map(lambda y: (y, set()), self.nodes))

        f = lambda x: self.isOrphan[x]
        orphans = list(filter(f, list(self.isOrphan)))

        if len(self.nodes) == 0:
            return False
        elif len(orphans) == 0:
            return True

        to_visit = deque(orphans)

        while len(to_visit) > 0:
            parent = self.nodes[to_visit.popleft()]
            visited.add(parent.name)

            for child in parent.arrowsTo:
                if child.name in ancestors_per_node[child.name]:
                    return True

                ancestors_per_node[child.name].add(parent.name)
                ancestors_per_node[child.name].update(ancestors_per_node[parent.name])
                to_visit.append(child.name)

        return not len(visited) == len(self.nodes)

class Problem:
    def __init__(self, qvq): #el qvq se pasa como lista de textos, no puede tener formulas repetidas (porque van a ser keys de algo).
        self.name = qvq
        for i in range(len(self.name)):
            self.name[i] = Formula("", [], self.name[i])
            self.name[i].toTree()
        self.PS = {} #diccionario que va a tener todos los PS (proof states) que se van generando. Las key van a ser el recorrido (qué hijos) que hay que hacer desde el ProofState adam (llamamos adam a la raíz de un árbol) para llegar al en cuestion (onda "0-0-1-0-2-1-5-"). EL adam tiene key = "".
        self.writeAdam()
        
        self.truths = {} #diccionario que va a tener como keys los nombres de las ramas de un arbol (formado por GraphNodes) y te va a mandar a una lista de teoremas o cosas asumidas.
        self.adam = GraphNode('')
        self.truths[''] = [] #esto hay que hacer que empiece siendo la lista de todos los teoremas que ya se conocen. Misma notacion que en el diccionario de PS.
        #agregar nocion de por que objetivos ya paso para que no loopee?
    
    def writeAdam(self):
        d = {}
        for i in range(len(self.name)):
            d[self.name[i].text] = ""
        self.PS[""] = ProofState(d, self.name, "eh?", "eh?", [], [], self)
        self.PS[""].findMetavariables('a')

#TO-DO: que cada proofstate este en orden alfabetico? (para facilidad de leer).
class ProofState:
    def __init__(self, truthDic, formulas, previousState, comesFrom, metavariables, name, problem): #el previousState tiene que ser "eh?" si no tiene ProofStates anteriores, o sea si es el adam. (TO-DO: volar assumptions e introducir truthDic. idem en writeAdam (en problem) y en expand).
        #self.assumptions = assumptions #lista de cosas asumidas. #(Esta vuela)
        self.formulas = formulas #lista de las formulas que hay que probar.
        self.truthDic = truthDic #va a tener como keys los textos de los elementos de formulas (TO-DO: asegurarme de que formulas no tenga elementos repetidos) y te manda a una key del truths del problem correspondiente.
        self.previousState = previousState #el name (del ProofState del que este vino). Si es el adam es un string en lugar de una lista, es "eh?"
        self.comesFrom = comesFrom #lista de dos elementos: el primero contiene el i de las formulas del ProofState anterior de la que vino, y el segundo contiene la regla de inferencia que se usó. Si este es el adam vale "eh?"
        self.metavariables = metavariables #contiene la lista de metavariables que aparecen en algún lado de este ProofState. Por ejemplo, ["a1", "a2", "a5"]. (TO-DO: que incluya a las que estan solo en el truths del Problem pero que tienen que ver con este PS).
        self.findMetavariables(['a'])
        self.name = name #lista de índices que hay que seguir en nextsStates desde el ProofState adam del Problem correspondiente para llegar a este ProofState. Si se lo pasa a texto con guiones entre números (y uno al final) te da su key en el diccionario PS de la clase Problem que corresponde.
        self.problem = problem
        
        self.nextsStates = [] #lista de posibles proximos PS.
    
    
    def findMetavariables(self, S): #hace que self.metavariables sea la lista de todas las metavariables (que empiezan con caracter en S) que hay en este ProofState, o sea, las que están en self.assumpions o en self.formulas. (Y devuelve esa lista). (TO-DO: que en vez de en assumtions las busque en el truths del Problem).
        self.metavariables = []
        #for assu in self.assumptions:
            #self.metavariables += assu.listVariables(S)
        for form in self.formulas:
            self.metavariables += form.listVariables(S)
        self.metavariables = list(dict.fromkeys(self.metavariables)) #esto elimina las repetidas.
        return self.metavariables
    
    
    def expand(self, i, infRule): #crea hijo de este ProofState que nace al aplicarle la regla de inferencia infRule a self.formulas[i]. TO-DO: que no pueda expandir dos veces con lo mismo (al pedo).
        #separar en el caso de que infRule sea la regla distinta o que sea la regla de "si feetea en algun teorema listo". TO-DO: en ambos casos modificar truthDic como corresponda.
        if i < len(self.formulas): #(esta linea vale la pena o mejor asumir que el i del imput esta en el rango correcto?)
            #TO-DO: pensar como terminar de programar lo de varList en feetea para que tenga sentido lo siguiente. (creo que ya ta).
            if feetea(self.formulas[i], infRule.conclusion, ["a", "p"], self.metavariables, infRule):
                self.nextsStates.append(ProofState(copy.deepcopy(self.truthDic), copy.deepcopy(self.formulas), self.name, [i, infRule], copy.deepcopy(self.metavariables), self.name + [len(self.nextsStates)], self.problem))
                
                k = self.nextsStates[-1].truthDic[self.nextsStates[-1].formulas[i].text]
                self.nextsStates[-1].truthDic.pop(self.nextsStates[-1].formulas[i].text)
                self.nextsStates[-1].formulas.pop(i)
                #(como hay que hacer si ya aparecen las formulas que toy por agregar? Me encargo despues desde el problem)
                for pre in infRule.premises:
                    self.nextsStates[-1].formulas.append(copy.deepcopy(pre))
                    self.nextsStates[-1].formulas[-1].replace()
                    self.nextsStates[-1].truthDic[self.nextsStates[-1].formulas[-1].text] = k
                self.nextsStates[-1].findMetavariables(['a'])
                self.nextsStates[-1].problem.PS[self.nextsStates[-1].toKey()] = self.nextsStates[-1]
                #agregar al PS del Problem correspondiente el par (key de este):este (creo que esto es la linea anterior)

    def expandCP(self, i): #crea hijo de este ProofState que nace al aplicarle la conditional proof a self.formulas[i], donde esa ultima tiene que ser de la forma ->(_,_) (una implicacion), o sea, esto arma un ProofState que es igual a este pero en vez de tener que probar P->Q hay que probar Q, asumiendo P.
        if i < len(self.formulas):
            if self.formulas[i].symbol == '->':
                self.nextsStates.append(ProofState(copy.deepcopy(self.truthDic), copy.deepcopy(self.formulas), self.name, [i, 'CP'], copy.deepcopy(self.metavariables), self.name + [len(self.nextsStates)], self.problem))
                
                
                k = self.nextsStates[-1].truthDic[self.formulas[i].text]
                #
                P = self.formulas[i].children[0]
                Q = self.formulas[i].children[0]
                #actualizar truthDic:
                #self.problem.
                
                #actualiza formulas:
                self.nextsStates[-1].formulas[i] = Q
                #
    
    
    def toKey(self): #devuelve el string correspondiente al name.
        k = ''
        for i in self.name:
            k += str(i) + '-'
        return k
    
    def show(self):
        print("----------------------------")
        print("this ProofState is:", self.name, ".")
        print("truthDic:", self.truthDic)
        print("formulas:", self.formulas)
        print("previousState:", self.previousState, ".")
        print("comesFrom:", self.comesFrom)
        print("metavariables:", self.metavariables)
        print("problem:", self.problem)
        print("list of nexts ProofStates:")
        for i in range(len(self.nextsStates)):
            print("\t", self.nextsStates[i].name)
        print("--------- thats it ----------")
    
    def __repr__(self):
        return str(self.name)
        

class Rule:
    def __init__(self, name, premises, conclusion):
        self.name = name
        self.premises = premises
        for p in self.premises:
            p.toTree()
        self.conclusion = conclusion
        self.conclusion.toTree()
    
    def __repr__(self):
        return self.name

def feetea(f, a, S, varList, infRule = False): #determina si se puede meter cosas adentro de f y de a (en las variables que empiezan con caracter en S) para que queden iguales. Por ejemplo, con s=["a"], feetean ^(a1,not(A1)) con ^(->(A2,A3),a2). varList es la lista de metavariables que ya aparecen en el ProofState en cuestión (está para que si se asignan metavariables no sean unas que ya estaban).
    global newVars
    newVars = []
    aAndpList(f, S)
    aAndpListAux(a, S)
    if not infRule == False:
        for prem in infRule.premises:
            aAndpListAux(prem, S)
    if feeteaAux(f, a, S):
        buildTheGraph(S)
        if G.hasLoops():
            fillGaps('a', varList)
            return chewForLoops('a', varList)
        else:
            fillGaps('a', varList)
            chew()
        return True
    else:
        return False

def feeteaAux(f, a, S):
    if not f.symbol[0] in S: #si el adam de f es un simbolo del sistema.
        if not a.symbol[0] in S: #si el adam de a es un simbolo del sistema.
            if not f.symbol == a.symbol: #si los adams de f y a son distintos.
                return False
            else: #si los adams de f y a son iguales.
                for i in range(len(f.children)):
                    if not feeteaAux(f.children[i], a.children[i], S):
                        return False
                return True
        else: #si el adam de a no es un simbolo del sistema.
            if extension[a.symbol] == []: #si no quedó nadie en la metavariable de a.
                extension[a.symbol].append(f)
                return True
            else: #si sí quedó alguien en la metavariable de a.
                return feeteaAux(f, extension[a.symbol][0], S)
    else: #si el adam de f no es un simbolo del sistema.
        if not a.symbol[0] in S: #si el adam de a es un simbolo del sistema.
            if extension[f.symbol] == []: #si no quedó nadie en la metavariable de f.
                extension[f.symbol].append(a)
                return True
            else: #si si quedó alguien en la metavariable de f.
                return feeteaAux(extension[f.symbol][0], a, S)
        else: #si el adam de a no es un simbolo del sistema.
            if f.symbol == a.symbol: #si son la misma metavariable.
                return True
            else: #si no son la misma metavariable.
                if extension[f.symbol] == [] and extension[a.symbol] == []: #si no quedó nadie en la metavariable de f ni en la de a.
                    if f.symbol == sorted([f.symbol, a.symbol])[0]:
                        extension[f.symbol].append(a)
                        return True
                    else:
                        extension[a.symbol].append(f)
                        return True
                elif not extension[f.symbol] == [] and extension[a.symbol] == []: #si quedó alguien en la metavariable de f y no quedó nadie en la de a.
                    extension[a.symbol].append(f)
                    return True
                elif extension[f.symbol] == [] and not extension[a.symbol] == []: #si quedó alguien en la metavariable de a y no quedó nadie en la de f.
                    extension[f.symbol].append(a)
                    return True
                else: #si quedó alguien en la metavariable de f y alguien en la de a.
                    return feeteaAux(extension[f.symbol][0], extension[a.symbol][0], S)

def aAndpList(f, S): #dada una formula f devuelve el diccionario cuyas key son todas las variables que ocurren (? en f y empiezan con un caracter en S (generalmente S es ['a', 'p']), y en cada key te devuelve la lista vacía.
    global extension
    extension = {}
    aAndpListAux(f, S)
    return extension

def aAndpListAux(f, S):
    if f.symbol[0] in S:
        if not f.symbol in extension:
            extension[f.symbol] = []
    for ch in f.children:
        aAndpListAux(ch, S)

def buildTheGraph(S): #arma el grafo cuyos nodos son las key de extension (salvo las key k tales que extension[k]=[]), y k apunta hacia j si j ocurre en el reemplazo de la metavariable k (o sea, si extension[k][0] contiene j)
    global G
    global d
    d = {}
    for k in extension:
        if not extension[k] == []:
            d[k] = GraphNode(k)
    for k in extension:
        if not extension[k] == []:
            d[k] = GraphNode(k)
            global l
            l = []
            buildTheGraphAux(extension[k][0], S)
            d[k].arrowsTo = l.copy()
    G = DGraph(d)

def buildTheGraphAux(N, S):
    if N.symbol[0] in S and N.symbol in d and not d[N.symbol] in l:
        l.append(d[N.symbol])
    for ch in N.children:
        buildTheGraphAux(ch, S)

def fillGaps(s, varList): #mira extension y los a los valores que tienen su lista vacia, le agregan una nueva a_i (o sea, una que no este en varList) (s es la letra que que quiero que se agregue con indices, en este caso 'a').
    i = 1
    for k in extension:
        if len(extension[k]) == 0:
            if k[0] == s:
                extension[k].append(Formula(k, [], k))
            else:
                while s+str(i) in varList or s+str(i) in extension: #esta condicion hay que pensarla bien cuando llamemos a esta funcion con las variables de los proofStates. El or lo puse para poder mientras ir probandola (la llamo con varList siendo []).
                    i += 1
                extension[k].append(Formula(s+str(i), [], s+str(i)))
                newVars.append(s+str(i))
                i += 1

def chew(): #cuando extension tiene exactamente un elemento por lista, esta funcion va agregando capas de elementos que cada uno es igual al anterior pero reemplazando cada metavariable que sea una key en extension por lo que tiene esa metavariable en la capa 0 de su lista en extension.
    numFinished = 0
    global extLayers
    extLayers = 1
    while numFinished < len(extension):
        for k in extension:
            newf = copy.deepcopy(extension[k][-1])
            newf = copy.deepcopy(chewAux(newf))
            extension[k].append(newf)
            if extLayers > 1:
                if extension[k][-1].text == extension[k][-2].text and not extension[k][-2].text == extension[k][-3].text:
                    numFinished += 1
            else:
                if extension[k][-1].text == extension[k][-2].text:
                    numFinished += 1
        extLayers += 1

def chewAux(f): #cuando extension tiene exactamente un elemento por lista, esta funcion va agregando capas de elementos que cada uno es igual al anterior pero reemplazando cada variable que sea una key en extension por lo que tiene esa variable en la capa 0 de su lista en extension.
    if f.symbol in extension:
        f = copy.deepcopy(extension[f.symbol][0])
    else:
        for i in range(len(f.children)):
            f.children[i] = copy.deepcopy(chewAux(f.children[i]))
    f.updateText()
    return f

#LE FALTA ASIGNAR NUEVAS a_i. (o ya se lo puse?)
def chewForLoops(s, varList): #es igual a chew, solo que esta se usa cuando el grafo tiene loops. Va controlando que si hay un loop no se agrande, o sea, que todos los loops sean de la forma "la metavariable k llego a tener que ser reemplazada por la variable k". (Y no por ejemplo que a1 sea reemplazado por ->(a1,(algo))). Ah, y ademas esta devuelve algo (True o False). s dice cual es la metavariable que tiene que usar para reemplazar los huecos (generalmente "a").   
    numFinished = 0
    global finalReplacing
    finalReplacing = {}
    for k in extension:
        finalReplacing[k] = []
    global extLayers
    extLayers = 1
    while numFinished < len(extension) and extLayers <= len(G.nodes):
        for k in extension: #agrega a extension[k] el último elemento que había en esa lista pero masticándolo una vez.
            newf = copy.deepcopy(extension[k][-1])
            newf = copy.deepcopy(chewAux(newf)) #(usa la misma auxiliar que chew()).
            extension[k].append(newf)
            if extension[k][-1].contains(k):
                if extension[k][-1].text == k:
                    if finalReplacing[k] == []:
                        finalReplacing[k].append([k][-1]) #lo agrega a finalReplacing si (no había nada todavia en ese lugar y) loopea sin agrandarse.
                        numFinished += 1
                else:
                    return False
            else:
                if extension[k][-1].text == extension[k][-2].text:
                    if finalReplacing[k] == []:
                        finalReplacing[k].append(extension[k][-1]) #lo agrega a finalReplacing si (no había nada todavia en ese lugar y) esta lista ya "convergió", o sea, si sus últimos dos elemenos son iguales.
                        numFinished += 1
        extLayers += 1
    global theLoops
    theLoops = [] #va a contener listas, cada una con las metavariables a las que hay que asigarle la misma nueva a_i.
    loopedVariables = [] #va a contener a las variables que, en el grafo, si seguis las flechas hacia adelante en algun momento volvés a sí misma.

    for k in finalReplacing:
        if len(finalReplacing[k]) != 0 and finalReplacing[k][0].text == k:
            loopedVariables.append(k)
            
    global lv
    lv = copy.deepcopy(loopedVariables)
    for i in range(len(lv)):
        if not lv[i] == "esteYaTa":
            theLoops.append([])
            spread(G, lv[i])
    i = 1
    for j in range(len(theLoops)):
        while s+str(i) in varList or s+str(i) in extension or s+str(i) in newVars: #de nuevo, esta condicion hay que pensarla bien cuando llamemos a esta funcion con las variables de los proofStates. El or lo puse para poder mientras ir probandola (la llamo con varList siendo []).
            i += 1
        for k in theLoops[j]:
            extension[k][0] = Formula(s+str(i), [], s+str(i))
            newVars.append(s+str(i))
        i += 1
    for k in extension:
        for _ in range(len(extension[k]) - 1):
            extension[k].pop(-1)
    chew()
    return True

def spread(g, n): #le metes un grafo (g) y el name (n) de uno de sus nodos y te busca a los que tiene conectado para adelante (dirección de las flechas) (y los agrega a la ultima lista de groups).
    theLoops[-1].append(n)
    for x in range(len(lv)):
        if lv[x] == n:
            lv[x] = "esteYaTa"
    for N in g.nodes[n].arrowsTo:
        if N.name in lv:
            spread(g, N.name)

f = Formula('^', [], '')
f.children.append(Formula('A', [], ''))
f.children.append(Formula('B', [], ''))
f.updateText()

f2 = Formula('->', [], '')
f2.children.append(Formula('a0', [], ''))
f2.children.append(Formula('a1', [], ''))
f2.updateText()
#print(f2.text)

f3 = Formula('V', [], '')
f3.children.append(Formula('^', [], ''))
f3.children.append(Formula('a1', [], ''))
f3.children[0].children.append(Formula('A', [], ''))
f3.children[0].children.append(Formula('B', [], ''))
f3.updateText()

'''
ps = ProofState()
ps.assumptions.append(f)
ps.formulas.append(f)

ps2 = ProofState()
ps2.assumptions.append(f2)
ps2.formulas.append(f2)
ps2.previousState = ps
'''

t0000 = Formula('', [], 'V(p2,p1)')
t0000.toTree()

t000 = Formula('', [], 'V(p1,p2)')
t000.toTree()

t0 = Formula('', [], 'a1')
t0.toTree()

t00 = Formula('', [], 'a2')
t00.toTree()

t01 = Formula('', [], '-->(a1,-->(a1,A1))')
t01.toTree()

t1= Formula('A1', [], '')
t1.updateText()

t2= Formula('A2', [], '')
t1.updateText()

t3 = Formula('', [], '^(A1,-->(A2,A3))')
t3.toTree()

t4 = Formula('', [], '^(a1,-->(a2,a3))')
t4.toTree()

t5 = Formula('', [], '^(p1,-->(p2,p3))')
t5.toTree()

t6 = Formula('', [], '-->(V(p1,p2),-->(p2,p3))')
t6.toTree()

t7 = Formula('', [], '-->(a1,-->(-->(A1,A2),a1))')
t7.toTree()

t8 = Formula('', [], 'a1')
t8.toTree()

t9 = Formula('', [], 'a2')
t9.toTree()

t10 = Formula('', [], '-->(a1,a2)')
t10.toTree()

t11 = Formula('', [], '-->(a2,a3)')
t11.toTree()

t12 = Formula('', [], '-->(a2,a1)')
t12.toTree()

t13 = Formula('', [], '-->(-->(a2,a1),-->(a4,a3))')
t13.toTree()

t14 = Formula('', [], '-->(-->(a4,a3),-->(a1,a2))')
t14.toTree()

t15 = Formula('', [], '-->(A2,A1)')
t15.toTree()

t16 = Formula('', [], 'V(A2,A1)')
t16.toTree()

t17 = Formula('', [], '-->(a1,-->(p1,a2))')
t17.toTree()

t18 = Formula('', [], '-->(p1,-->(a2,a3))')
t18.toTree()

t19 = Formula('', [], '-->(a1,a2)')
t19.toTree()

t20 = Formula('', [], '-->(->(a2,a2),A1)')
t20.toTree()

t21 = Formula('', [], '-->(^(a1,a2),^(p1,p2))')
t21.toTree()

t22 = Formula('', [], '-->(^(V(A1,not(a2)),not(A1)),^(^(not(A3),not(not(A2))),p2))')
t22.toTree()

t23 = Formula('', [], '->(a1,a2)')
t23.toTree()

t24 = Formula('', [], '->(a2,a1)')
t24.toTree()

t25 = Formula('', [], '->(a1,a2,a3,a4,a5)')
t25.toTree()

t26 = Formula('', [], '->(a2,a3,a4,a5,a1)')
t26.toTree()

t27 = Formula('', [], '->(V(a2,a2),V(a3,a3),V(A1,A1))')
t27.toTree()

t28 = Formula('', [], '->(a2,a3,a4,a5,a3)')
t28.toTree()

t29 = Formula('', [], '->(->(a2,a3),A1,a4,a5,a1)')
t29.toTree()

t30 = Formula('', [], '->(a1,A1)')
t30.toTree()

t31 = Formula('', [], '->(->(a2,a3,a4,a5,a6),a2)')
t31.toTree()

t32 = Formula('', [], '->(a2,a3,a1,a5,a4)')
t32.toTree()

t33 = Formula('', [], '->(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26)')
t33.toTree()

t34 = Formula('', [], '->(a2,a3,A1,a4,a6,a7,a5,a9,a10,^(a11,a12,a13),A1,a14,a15,a12,a16,a13,a18,a19,a18,a21,V(a22,a23),a23,a24,A1,a26,a25)')
t34.toTree()

t35 = Formula('', [], '->(a1,a2,a3,a4,a5,a6,a7,a8,a9)')
t35.toTree()

t36 = Formula('', [], '->(a2,a3,a1,a5,a6,a5,a7,a9,a8)')
t36.toTree()

t37 = Formula('', [], '->(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10)')
t37.toTree()

t38 = Formula('', [], '->(a2,a3,a1,a5,a6,a5,a7,a9,a10,a8)')
t38.toTree()

t39 = Formula('', [], '->(a1,a2,a3,a4,a5,a6,a7,a8,a9,a90,a91,a92,a93,a94,a95,a96,a97,a98,a99,a990,a991,a992,a993,a994,a995,a996)')
t39.toTree()

t40 = Formula('', [], '->(a2,a3,A1,a4,a6,a7,a5,a9,a90,^(a91,a92,a93),A1,a94,a95,a92,a96,a93,a98,a99,a98,a991,V(a992,a993),a993,a994,A1,a996,a995)')
t40.toTree()

t41 = Formula('', [], '^(->(p1,p1),V(p2,~(p2)))')
t41.toTree()

t42 = Formula('', [], '^(A1,A2)')
t42.toTree()

t43 = Formula('', [], '~(~(->(p1,p1)))')
t43.toTree()

t44 = Formula('', [], '~(A1)')
t44.toTree()

t45 = Formula('', [], '+(*(m1,x),b1)')
t45.toTree()

t46 = Formula('', [], '+(4,5)')
t46.toTree()

t47 = Formula('', [], 'b1')
t47.toTree()

t48 = Formula('', [], '+(b1,b1)')
t48.toTree()

t49 = Formula('', [], '+(*(m1,x),b1)')
t49.toTree()

t50 = Formula('', [], '+([1,/(.1,0))')
t50.toTree()

n1 = GraphNode('n1')
n2 = GraphNode('n2')
n3 = GraphNode('n3')
n4 = GraphNode('n4')
n5 = GraphNode('n5')

n1.arrowsTo.append(n2)
n3.arrowsTo.append(n4)
n4.arrowsTo.append(n5)
n5.arrowsTo.append(n1)

gr = DGraph({'n1': n1,'n2': n2, 'n3': n3, 'n4': n4, 'n5': n5})



r1 = Rule("r", [Formula('', [], "p1"), Formula('', [], "p2"), Formula('', [], "V(p3,p4)"), Formula('', [], "^(p5,p6)")], Formula('', [], "^(p1,p2)"))
r2 = Rule("r", [Formula('', [], "p1")], Formula('', [], "V(p1,p2)"))

#infRules = []
#infRules.append(Rule('Neation introduction', [Formula('', [], "->(p1,p2)"), Formula()]))

#prob = Problem(["^(V(A1,~(A1)),->(~(A2),A2))"])


symbols = ["!", "->", "-->", "^", "V", "<->", "A1", "A2", "a1", "a2", "a3", "a4", "p1", "p2", "p3"]

def randomFormula():
    s = symbols[random.randint(0, len(symbols)-1)]
    f = Formula(s, [], "")
    if f.symbol[0] in ["a", "p", "A"]:
        f.updateText()
        return f
    elif f.symbol == "!":
        f.children.append(randomFormula())
        f.updateText()
        return f
    else:
        for _ in range(2):
            f.children.append(randomFormula())
        f.updateText()
        return f

def reemplazar(a):
    if a.symbol in extension:
        a = copy.deepcopy(extension[a.symbol][-1])
        return a
    else:
        for i in range(len(a.children)):
            a.children[i] = copy.deepcopy(reemplazar(a.children[i]))
        a.updateText()
        return a

#testeé feetea con 10^4 pares de formulas random, y de los 6123 casos en los que el par feetea LOS 6123 FEETEAN POSTA :D
def testearFeetea(N):
    se = 0
    no = 0
    siBien = 0
    siMal = 0
    for i in range(N):
        if i%1000 == 0:
            print (i, "de", N)
        a = randomFormula()
        b = randomFormula()
        if feetea(a, b, ["a", "p"], []):
            se += 1
            if reemplazar(a).text == reemplazar(b).text:
                siBien += 1
            else:
                siMal += 1
        else:
            no += 1
    print(se, "se ("+str(siBien), "bien y", siMal, "mal), ", no, "no")


Theorems = ["^(->(A1,A2),A1)"] #lista de strings
Aindex = [] #lista de indices de las cosas de Theorems que son asumidas.

#https://en.wikipedia.org/wiki/Propositional_calculus#Example_2._Natural_deduction_system

InfRules = {}
InfRules["Negation introduction"] = Rule("Negation introduction", [Formula('', [], "->(p1,p2)"), Formula('', [], "->(p1,~(p2))")], Formula('', [], "~(p1)"))
InfRules["Negation elimination"] = Rule("Negation elimination", [Formula('', [], "~(p1)")], Formula('', [], "->(p1,p2)"))
InfRules["Double negation elimination"] = Rule("Double negation elimination", [Formula('', [], "~(~(p1))")], Formula('', [], "p1"))
InfRules["Conjunction introduction"] = Rule("Conjunction introduction", [Formula('', [], "p1"), Formula('', [], "p2")], Formula('', [], "^(p1,p2)"))
InfRules["Conjunction elimination izq"] = Rule("Conjunction elimination izq", [Formula('', [], "^(p1,p2)")], Formula('', [], "p1"))
InfRules["Conjunction elimination der"] = Rule("Conjunction elimination der", [Formula('', [], "^(p1,p2)")], Formula('', [], "p2"))
InfRules["Disjunction introduction izq"] = Rule("Disjunction introduction izq", [Formula('', [], "p1")], Formula('', [], "V(p1,p2)"))
InfRules["Disjunction introduction der"] = Rule("Disjunction introduction der", [Formula('', [], "p2")], Formula('', [], "V(p1,p2)"))
InfRules["Disjunction elimination"] = Rule("Disjunction elimination", [Formula('', [], "V(p1,p2)"), Formula('', [], "->(p1,p3)"), Formula('', [], "->(p2,p3)")], Formula('', [], "p3"))
InfRules["Biconditional introduction"] = Rule("Biconditional introduction", [Formula('', [], "->(p1,p2)"), Formula('', [], "->(p2,p1)")], Formula('', [], "<->(p2,p1)"))
InfRules["Biconditional elimination ->"] = Rule("Biconditional elimination ->", [Formula('', [], "<->(p1,p2)")], Formula('', [], "->(p1,p2)"))
InfRules["Biconditional elimination <-"] = Rule("Biconditional elimination <-", [Formula('', [], "<->(p1,p2)")], Formula('', [], "->(p2,p1)"))
InfRules["Modus ponens"] = Rule("Modus ponens", [Formula('', [], "p1"), Formula('', [], "->(p1,p2)")], Formula('', [], "p2"))


prob = Problem(["a1", "->(a1,^(A1,a2))", "<->(A1,A1)"])


def goForward(r, ind): #le metes una Rule (r) y una lista de indices (ind) y se fija si los Theorems con indice en ind feetean, en ese orden, con las premisas de r. Si si, agrega la conclusion de r a Theorems, reemplazando las metavariables por lo que terminan teniendo en el feeteo. Si quedan metavariables en la conclusion sin reemplazar (por ejemplo en Negation elimination) le pregunta al usuarie que le quiere meter.
    if len(ind) == len(r.premises):
        x1=".("
        x2=".("
        for i in range(len(ind)-1):
            x1 += r.premises[i].text + ","
            x2 += Theorems[ind[i]] + ","
        x1 += r.premises[-1].text + ")"
        x2 += Theorems[ind[-1]] + ")"
        x1 = Formula('', [], x1)
        x1.toTree()
        x2 = Formula('', [], x2)
        x2.toTree()
        if feetea(x1, x2, ['p'], []):
            a = copy.deepcopy(r.conclusion)
            a = copy.deepcopy(reemplazar(a))
            a.listVariables(['p'])
            for m in a.variables:
                texto = "Que queres que sea " + m + "?"
                extension[m] = [Formula('', [], input(texto))]
                extension[m][0].toTree()
            a = copy.deepcopy(reemplazar(a))
            Theorems.append(a.text)
                
        else:
            print("No feetean corazon")
    else:
        print("salame nececitas meter", len(r.premises), "teoremas")

def goForwardCP(assum): #(Conditional proof, la ultima regla, la distinta)
    Aindex.append(len(Theorems))
    Theorems.append(assum)

def closeLastAssumption(i):
    Theorems[Aindex[-1]] = "->(" + Theorems[Aindex[-1]] + "," + Theorems[i] + ")"
    for j in range(Aindex[-1]+1, len(Theorems)):
        Theorems.pop()
    Aindex.pop()
