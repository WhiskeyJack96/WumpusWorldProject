from enum import Enum
from Agent import Agent
import heapq
from itertools import product

class _pq:
    """A simple priority Queue implimentation for A*"""
    def __init__(self):
        self.pq = []
    def empty(self):
        return self.pq == []
    def enqueue(self, item, priority):
        heapq.heappush(self.pq, (priority, item))
    def dequeue(self):
        return heapq.heappop(self.pq)[1]

class _MyTile:
    """A Printable Tile object, used in the map, keeps track of what is known and suspected about locations"""
    def __init__(self, smell=False, breeze=False, pit=False, wumpus=False, wall=False, visited = False):
        self.smell = smell
        self.breeze = breeze
        self.pit = pit
        self.wumpus = wumpus
        self.potentialWump = False
        self.wall=wall
        self.visited=visited
        self.safe = False
    def __repr__(self):
        temp = ' '
        if(self.wall):
            temp+= '-'
        if(self.pit):
            temp +='p'
        if(self.wumpus):
            temp +='W'
        if(self.potentialWump):
            temp += 'w'
        if(self.breeze):
            temp +='b'
        if(self.smell):
            temp+='s'
        if(self.visited):
            temp += 'v'
        if(self.safe):
            temp += 'S'
        return temp
    def setSafe(self):
        self.safe = True


class MyAI ( Agent ):
    """AI extends Agent which was provided. Agent contains definitions for actions as an enum class as well as an abstract definition of the getAction Method"""
    def __init__ ( self):

        #Defines directions so that turning is just incrimenting or decrimenting the current direction
        self.left = 2
        self.right= 0
        self.down=1
        self.up=3

        #Starting location is the bottom left corner of the map. For simplicity this is the bottom left corner of the 2 dimensional list self.gameboard
        self.currentLocation = (10,1)
        #gameboard[0][x] is a row
        #gameboard[x][0] is a column
        #gameboard is a 2d list of tiles. size 12 is chosen because the ai must be able to run on up to size 10 boards (with two walls on each side)
        #This greatly simplified the agents wall interaction logic
        self.gameboard = [[_MyTile() for i in range(12)]for i in range(12)]
        
        #sets the leftmost column and bottom most row to be walls since they always will be
        for i in self.gameboard[11]:
            i.wall = True
        for i in self.gameboard:
            i[0].wall = True
        
        #intial information specific to this description of wumpus world project
        #Agent always faces right at the start
        self.facing = self.right
        #Agent never starts with gold
        self.hasGold = False
        #Agent never starts with a dead wumpus
        self.killedWump = False
        #used for storing paths to destinations
        self.moveQueue = []
        #used for storing tiles that have yet to be visited that are safe
        self.unvisitedSafe= []
        #used for probability calculations. This is a subset of unvisited safe
        self.frontier = set()
        #This is an exclusion set to prevent tiles from being revisited
        self.xset = set()

        #more initializations, never have shot when starting
        self.shot = False
        #The following are initializations for the hunting code, they are initalized such that if the agent never finds the wumpus then the agent will not hunt and will instead return to the start
        self.wumpuslocation = (10,1)
        self.safetoshoot = (10,1)
        self.hunting = False

        #used for tracking actions 
        self.lastAction = None
        
    def getAction( self, stench, breeze, glitter, bump, scream ):
        #gets, and updates the current tile as safe visited and pit free. These are necessary because the agent can choose to move to an unsafe tile if the risk is low
        current = self.gameboard[self.currentLocation[0]][self.currentLocation[1]]
        self.frontier.discard(self.currentLocation)
        current.visited = True
        current.safe = True
        current.pit = False

        #if chain for each precept. Each statement updates the knowledge base, some exit early for simplicities sake (agent will always pick up gold first)
        #update* methods all set the tile information for the provided precept
        #potentialWump is a dummy precept used to differentiate between when the agent knows where the wumpus is and when it has a guess for where the wumpus is
        if(glitter):
            self.hasGold = True
            self.moveQueue = self.pathToList(self.findPathAStar(self.currentLocation, (10,1), self.facing)[0], (10,1))
            return Agent.Action.GRAB
        if(bump):
            di = self.getForward()
            self.currentLocation = self.currentLocation[0] - di[0],self.currentLocation[1] - di[1]
            self.updateFront("wall")
            self.moveQueue = []
        if(scream):
            self.killedWump = True
            self.updateAll("wumpus")
            self.updateAll("potentialWump")
        if(breeze):
            current.breeze = True
            self.updateAdjacent("pit")
        #uses first order logic to determine wumpus locations. wumpus -> stench(adjacent), thus if the agent has two stenches it can determine the exact location of the wumpus
        #Agent can also shoot wumpus, agent will gamble on shooting the wumpus if it percieves a stench in the first tile. in the worst case this is a wash in terms of expected return so it is worthwile to risk
        #shooting costs -10, gold has a 1/number of tiles chance of being anywhere, for a 10x10 there are 100 tiles. 1000/100 ==10.
        if(stench):
            if( not self.killedWump):
                current.smell = True
                self.updateWumpus()
                if(not self.shot and self.currentLocation == (10,1) and not current.breeze):
                    self.lastAction = "SHOOT"
                    self.shot = True
                    return Agent.Action.SHOOT
                if(self.lastAction == "SHOOT"):
                    self.lastAction = None
                    self.updateFront("wumpus")
                if(not self.shot and self.numberW() == 1 and not self.hasGold):
                    turn = self.checkDirection(self.wumpuslocation)
                    if(turn == 0):
                        self.shot = True
                        return Agent.Action.SHOOT
                    else:
                        if(turn ==1 or turn == -3):
                            self.updateFacing('left')
                            return Agent.Action.TURN_LEFT
                        else:
                            self.updateFacing('right')
                            return Agent.Action.TURN_RIGHT

        #if the tile lacks these precepts all tiles adjacent should be safe        
        if(not breeze and not stench):
            self.updateAdjacent("safe")
        #allows the agent to keep track of what tiles may have wumpus for shooting purposes
        if(not breeze and stench):
            self.updateAdjacent("wsafe")

        #if the character is at destination remove the destination from the Queue
        if(self.moveQueue != [] and self.moveQueue[0] == self.currentLocation):
            self.moveQueue.pop(0)

        #if there are no moves left in the queue search the map for any that have become safe. start hunting if no other moves remain
        if(self.unvisitedSafe == [] ):
            if(not self.searchForUnvisited() and self.moveQueue == [] and not self.hunting and not self.shot):
                self.hunting = True
                self.unvisitedSafe.append(self.safetoshoot)

        #calculates that probability that there is a hole in each suspect tile using bayes rule. then calculates the value of the risk based on utility theory.
        #Takes risk that are more valuable than 30. Chosen by analyzing gameboards that are not worthwhile and calculating their utility and then incrimenting by 1
        #this value stops the agent from exploring the situation where there is a breeze in both 10,2 and 9,1, since it is unlikely to yeild the gold
        if(self.unvisitedSafe == [] and self.moveQueue == []):
            problist = []
            loclist = []
            if(len(self.frontier) >1):
                for loc in self.frontier:
                    problist.append(self.findHoleProbability(loc))
                    loclist.append(loc)
            numUnvisit = self.numberUnvisited()
            utilityOfGold = 1000. / numUnvisit
            if(problist != [] and (max(problist) * utilityOfGold)>30):
                j = loclist[problist.index(max(problist))]
                self.gameboard[j[0]][j[1]].safe = True

        #determines when to climb
        if((self.hasGold or ((self.unvisitedSafe == [] or self.unvisitedSafe == [(10,1)]) and self.moveQueue == [])) and self.currentLocation == (10,1)):
            return Agent.Action.CLIMB 
        
        ##If the move Queue is empty run astar to find a new destination
        if(self.moveQueue ==[]):
            if(self.unvisitedSafe ==[]):
                path, cost = self.findPathAStar(self.currentLocation, (10,1), self.facing)
                dest = (10,1)
            else:
                self.unvisitedSafe = self.smartSort(self.unvisitedSafe)
                dest = self.unvisitedSafe.pop(0)
                path, cost = self.findPathAStar(self.currentLocation, dest, self.facing)
            self.moveQueue = self.pathToList(path, dest)

        ##if the Q isnt empty determine the proper move to advance toward the goal
        if(self.moveQueue != []):
            self.nextMove = self.moveQueue[0]
            turnsNeeded = self.checkDirection(self.nextMove)
            if(turnsNeeded== 0):
                self.currentLocation = self.checkForward()
                return Agent.Action.FORWARD
            else:
                if(turnsNeeded ==1 or turnsNeeded == -3):
                    self.updateFacing('left')
                    return Agent.Action.TURN_LEFT
                else:
                    self.updateFacing('right')
                    return Agent.Action.TURN_RIGHT

    #updates self.facing based on the direction that is being turned
    def updateFacing(self, di):
        if(di == "left"):
            if(self.facing == 0):
                self.facing = 3
            else:
                self.facing-=1
 
        elif(di == "right"):
            if(self.facing == 3):
                self.facing = 0
            else:
                self.facing+=1

    #Calculates an estimated number of unvisited tiles for utility calculations
    def numberUnvisited(self):
        temp = 0
        for i in self.gameboard:
            for j in i:
                if(j.visited):
                    temp +=1
        if(temp > 31):
            return 52 - temp
        return 32 - temp

    #preforms logical analysis to determine where the wumpus is/may be
    def updateWumpus(self):
        wumplist = []
        mhit = 0
        for i in [(1,0),(0,1),(-1,0),(0,-1)]:
            potentialWump = self.currentLocation[0] +i[0], self.currentLocation[1] + i[1]
            if(not self.isInBounds(potentialWump) or self.gameboard[potentialWump[0]][potentialWump[1]].safe):
                continue
            hit = 0
            for j in [(1,0),(0,1),(-1,0),(0,-1)]:
                needStench = potentialWump[0] +j[0], potentialWump[1] + j[1]
                if(self.isInBounds(needStench)):
                    if(self.gameboard[needStench[0]][needStench[1]].smell):
                        hit +=1

            if(hit >mhit):
                mhit = hit
                wumplist.clear()
                wumplist.append(potentialWump)
            elif(hit == mhit):
                wumplist.append(potentialWump)
        if(len(wumplist)==1):
            self.gameboard[wumplist[0][0]][wumplist[0][1]].wumpus = True
            self.safetoshoot = self.currentLocation 
            self.wumpuslocation = wumplist[0]
            self.updateAll('potentialWump')
        else:
            for x in wumplist:
                self.gameboard[x[0]][x[1]].safe = False
                self.gameboard[x[0]][x[1]].potentialWump = True
                        
    #counts the nnumber of tiles marked to have the wumpus, for shooting logic
    def numberW(self):
        num = 0
        for row in self.gameboard:
            for tile in row:
                if(tile.wumpus):
                    num +=1
        return num

    #calculates the probability that there is a breeze in a given tile, given that there is a breeze adjacent to it and given the frontier of unexplored squares
    #does this by summing over consistent possible worled to calculated the probability based on bayes law
    def findHoleProbability(self,loc):
        Hole = .2
        frontier = list(self.frontier)
        frontier.remove(loc)
        possibleWorlds = set(product([True, False], repeat = len(frontier)))
        self.gameboard[loc[0]][loc[1]].pit =False
        noPitProb = 0
        for world in possibleWorlds:
            if(self.isConsistent(world, frontier)):
                noPitProb += (Hole ** world.count(True)) * ((1-Hole)**world.count(False))
                #print(world, noPitProb)
        self.gameboard[loc[0]][loc[1]].pit =True
        PitProb = 0
        for world in possibleWorlds:
            if(self.isConsistent(world, frontier)):
                PitProb += Hole ** world.count(True) * (1.0-Hole)**world.count(False)
        rawprob = ((1-Hole)*noPitProb, Hole * PitProb)
        norm = (rawprob[0] + rawprob[1])
        if(norm <= 0):
            return 0 
        norm = 1/norm
        return rawprob[0] * norm

    #determines if a given world and frontier are consistent ie there is a pit adjacent to ever breeze
    def isConsistent(self, world, frontier):
        tempGameboard = [x[:] for x in self.gameboard]
        for i,j in zip(world,frontier):
            tempGameboard[j[0]][j[1]].pit = i
        for i in range(len(tempGameboard)):
            for j in range(len(tempGameboard[i])):
                 if(tempGameboard[i][j].breeze):
                    if(not self.checkAdjacentPit((i,j), tempGameboard)):
                        return False
        return True

    #checks if there is a pit adjacent to a given gamestate(gb)
    def checkAdjacentPit(self, loc, gb):
        for i in [(1,0), (-1,0),(0,1),(0,-1)]:
            pitloc = loc[0] + i[0], loc[1] + i[1]
            if(self.isInBounds(pitloc)):
                if(gb[pitloc[0]][pitloc[1]].pit):
                    return True
        return False

    #converts a path dictionary (as given by A*) to a list
    def pathToList(self, pathdict, dest):
        temp = [dest]
        while(dest !=None):
            temp.append(pathdict[dest])
            dest = pathdict[dest]
        temp.reverse()
        return temp[2:]

    #sorts potential moves by the cost of the moves (ie number of turns and manhattan distance)
    def smartSort(self, moves):
        moves = sorted(moves, key = lambda x: abs(abs(self.checkDirection(x) )-2),reverse =True)
        return sorted(moves, key =lambda x: abs(x[0] -self.currentLocation[0]) + abs(x[1] - self.currentLocation[1]))

    #manhattan distance hueristic for A*
    def _hueristic(self, a, b):
        x1,y1 = a
        x2,y2 = b
        return (abs(x1-x2)+abs(y1-y2))

    #return the neighbors of a tile if they are safe and inbounds, used for A*
    def getNeighbors(self, location):
        neighbors = []
        ## finds neighbors that are adjacent but still in the graph
        for i in [(1,0), (-1,0),(0,1),(0,-1)]:
            neighbor = location[0] + i[0], location[1] + i[1]
            if(neighbor[0] >0 and neighbor[0] <11 and neighbor[1] >0 and neighbor[1]<11 and self.gameboard[neighbor[0]][neighbor[1]].safe):
                neighbors.append(neighbor)

        return neighbors

    #A* pathfinding algorithm, uses manhattan distance and turn cost to estimate path costs. 
    def findPathAStar(self, start, destination, facing):
        frontier = _pq()
        frontier.enqueue(start, 0)
        path = {}
        pathCost = {}
        direction = {}
        path[start] = None
        pathCost[start] = 0
        direction[start] = facing
        while(not frontier.empty()):
            current = frontier.dequeue()
            if(current == destination):
                break
            for nextn in self.getNeighbors(current):
                turncost =  self.calcTurns(direction[current], current, nextn)
                cost = pathCost[current] + 1 + turncost[0]
                if(nextn not in pathCost or cost < pathCost[nextn]):
                    pathCost[nextn] = cost
                    direction[nextn] = turncost[1]
                    priority = cost + self._hueristic(nextn, destination)
                    frontier.enqueue(nextn, priority)
                    path[nextn] = current
        return path, pathCost

    #calculates the number of turns needed for A*
    def calcTurns(self, direction, current, dest):
        temp = -current[0] + dest[0], -current[1] + dest[1]
        facing = self.getFacing(temp)
        nturn = facing - direction
        if(abs(nturn)==3):
            return 1,facing
        return abs(nturn),facing

    #updates the tile in front given a precept
    def updateFront(self, sensor):
        direction = self.getForward()
        forward = (self.currentLocation[0]+direction[0], self.currentLocation[1]+direction[1])
        if(sensor == "wumpus"):
            self.gameboard[forward[0]][forward[1]].potentialWump = False
            self.gameboard[forward[0]][forward[1]].wumpus = False
            self.gameboard[forward[0]][forward[1]].safe = True
        if(sensor == "wall"):
            self.gameboard[forward[0]][forward[1]].wall = True
            if(self.facing==0):
                for i in self.gameboard:
                    for j in range(forward[1], 12):
                        i[j].wall = True
            elif(self.facing==3):
                for j in range(0, forward[0]+1):
                    for i in self.gameboard[j]:
                        i.wall = True

    #updates adjactent tiles given a precept
    def updateAdjacent(self, sensor):
        for i in [(1,0), (-1,0),(0,1),(0,-1)]:
            xy = self.currentLocation[0] + i[0], self.currentLocation[1] + i[1]
            loc = self.gameboard[xy[0]][xy[1]]

            if(not loc.wall and not loc.visited and sensor == "pit"):
                self.frontier.add(xy)

            if((sensor == "wsafe") and loc.wall == False and loc.visited==False and not loc.safe and not loc.wumpus and not loc.potentialWump):
                setattr(loc, 'safe',True)
            elif((sensor == "safe") and loc.wall == False and loc.visited==False and not loc.safe):
                setattr(loc,sensor,True)
            elif(loc.wall == False and loc.visited==False and not loc.safe):
                setattr(loc,sensor,True)
            if(sensor in ['safe', 'wsafe']):
                if(self.isInBounds(xy) and not loc.wall and (not loc.visited) and not loc.wumpus and not loc.potentialWump and not (xy in self.xset)):
                    self.unvisitedSafe.append(xy)
                    self.xset.add(xy)

    #checks if a tile is in bounds
    def isInBounds(self, loc):
        x = loc[0]
        y = loc[1]
        return x<11 and x>0 and y<11 and y>0 and not self.gameboard[x][y].wall

    #checks if adjacent tiles are safe and not walls
    def checkAdjacent(self):
        for i in [(1,0), (-1,0),(0,1),(0,-1)]:
            loc = self.gameboard[self.currentLocation[0] + i[0]][self.currentLocation[1] + i[1]]
            if(loc.wumpus == False and loc.pit == False and loc.wall == False):
                return True
        return False

    #updates all given a precept, used primarily for scream precept when wumpus dies
    def updateAll(self, sensor, boo= False):
        for i in self.gameboard:
            for j in i:
                if(getattr(j, sensor)):
                    setattr(j, sensor,boo)
                    if(not j.pit and not j.wumpus and not j.wall):
                        setattr(j, "safe", True)

    #checks the front tile is safe, returns error if not 
    def checkForward(self):
        direction = self.getForward()
        forward = (self.currentLocation[0]+direction[0], self.currentLocation[1]+direction[1])
        forwardTile = self.gameboard[forward[0]][forward[1]]
        if(forwardTile.safe):
            return forward
        else:
            return (0,0)

    #gets the list direction of a given direction
    def getForward(self):
        if(self.facing == self.left):
            return  (0,-1)
        if(self.facing == self.right):
            return (0,1)
        if(self.facing == self.down):
            return (1,0)
        if(self.facing == self.up):
            return (-1,0)

    #returns left,right,up,down based on list direction
    def getFacing(self, di):
        if(di == (1,0)):
            return 1
        if(di == (0,-1)):
            return 2
        if(di == (-1,0)):
            return 3
        if(di == (0,1)):
            return 0

    #used to normalize tuples in order to determine directions
    def _normalizeTuple(self, tup):
        first = 0
        second = 0
        if(tup[0] != 0):
            first = tup[0]/abs(tup[0])
        if(tup[1] != 0):
            second = tup[1]/abs(tup[1])
        return first,second

    #determines the number of turns required to face a particular direction
    def checkDirection(self, dest):
        temp = -self.currentLocation[0] + dest[0], -self.currentLocation[1] + dest[1]
        facing = self.getFacing(self._normalizeTuple(temp))
        if(facing != None):
            return self.facing - facing
        else:
            return 2
    #appends all unvisited tiles to self.unvisitedSafe, returns boolean for checking purposes
    def searchForUnvisited(self):
        for i in range(len(self.gameboard)):
            for j in range(len(self.gameboard[i])):
                loc = self.gameboard[i][j]
                if((not loc.visited) and loc.safe and not ((i,j) in self.xset) ):
                    self.unvisitedSafe.append((i,j)) 
                    self.xset.add((i,j))
        return self.unvisitedSafe != []