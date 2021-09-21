import z3, copy, json

# Purpose: To generate all the possibilties for a given team to qualify

# Load the current W L Diff for played matches
# Calculate for the specific team, to see min score needed to qualify
# For all future matches, find all combinations that satisfy that min score

# Disregard tie breakers for now

class Game:
    def __init__(self, team1, team2):
        self.team1 = team1
        self.team2 = team2

class Team:
    def __init__(self, name, win, loss, diff, region):
        self.name = name
        self.win = win
        self.loss = loss
        self.diff = diff
        self.region = region

class Scenario:
    def __init__(self, team, pos, win, loss, diff, region):
        self.name = team
        self.pos = pos
        self.win = win
        self.loss = loss
        self.diff = diff
        self.region = region

# Constants
upcoming_games = [
    Game("PAR", "TOR"),
    Game("FLA", "HOU"),
    Game("LDN", "PAR"),
    Game("SFS", "VAN"),
    Game("FLA", "GLA"),
    Game("LDN", "VAN"),
    Game("GLA", "HOU"),
    Game("SFS", "TOR"),
]

# Figure out the points tally and score at the end of the stage
teams = [
    Team("ATL", 4, 0, 7, "WEST"),
    Team("TOR", 2, 0, 5, "WEST"),
    Team("DAL", 2, 2, 0, "WEST"),
    Team("GLA", 1, 1, 2, "WEST"),
    Team("SFS", 1, 1, 1, "WEST"),
    Team("FLA", 1, 1, 1, "WEST"),
    Team("HOU", 1, 1, 0, "WEST"),
    Team("VAN", 1, 1, 0, "WEST"),
    Team("PAR", 1, 1, -1, "WEST"),
    Team("BOS", 1, 3, -5, "WEST"),
    Team("WAS", 1, 3, -6, "WEST"),
    Team("LDN", 0, 2, -4, "WEST")
]

def initSolver():
    z3.set_option('smt.random_seed', 0)
    S = z3.Solver()

    # Encode constraints on the number of points that can be scored in each game
    for g in upcoming_games:
        g.team1score = z3.Int(g.team1 + "-" + g.team2)
        g.team2score = z3.Int(g.team2 + "-" + g.team1)
        S.add(g.team1score >= 0)
        S.add(g.team1score <= 3)
        S.add(g.team2score >= 0)
        S.add(g.team2score <= 3)
        S.add(g.team1score + g.team2score <= 5)
        S.add(z3.Or(g.team1score == 3, g.team2score == 3))

    for t in teams:
        # select the relevant games for this team
        currentT1TeamGames = [g for g in upcoming_games if g.team1 == t.name]
        # count the number of points
        t1points = sum([
            z3.If(g.team1score > g.team2score, 1, 0) for g in currentT1TeamGames
        ])
        t1differential = sum([g.team1score - g.team2score for g in currentT1TeamGames])

        # do the same for team2
        currentT2TeamGames = [g for g in upcoming_games if g.team2 == t.name]
        t2points = sum([
            z3.If(g.team2score > g.team1score, 1, 0) for g in currentT2TeamGames
        ])
        t2differential = sum([g.team2score - g.team1score for g in currentT2TeamGames])

        # final points
        t.finalPoints = t1points + t2points + t.win
        t.finalMapDiff = t1differential + t2differential + t.diff

    # specific position must be between 1 and n
    for t in teams:
        # absolute positions
        t.position = z3.Int(t.name + '_pos')
        S.add(t.position >= 1)
        S.add(t.position <= len(teams))

    # relative positions
    for i in range(len(teams)):
        ti = teams[i]
        for j in range(len(teams)):
            tj = teams[j]
            if i == j: continue

            # more points => higher finish
            S.add(z3.Implies(ti.finalPoints > tj.finalPoints, ti.position < tj.position))
            # equal points and better map difference => higher finish
            S.add(z3.Implies(
                z3.And(ti.finalPoints == tj.finalPoints, ti.finalMapDiff > tj.finalMapDiff),
                ti.position < tj.position))
            # no two teams can have the same position.
            if i < j:
                S.add(ti.position != tj.position)
    
    return S

def teamMustQualify(S, name):
    team_lst = list(filter(lambda t: t.name == name, teams))
    if team_lst[0].region == "WEST":
        S.add(team_lst[0].position <= 6)
    else:
        S.add(team_lst[0].position <= 4)
    return S

def teamWinsMatch(S, winningTeam, losingTeam):
    teamNames = list(map(lambda x: x.name, teams))
    if winningTeam in teamNames and losingTeam in teamNames:
        S.add(z3.Int(winningTeam + "-" + losingTeam) == 3)
    return S

def teamSweepMatch(S, winningTeam, losingTeam):
    teamNames = list(map(lambda x: x.name, teams))
    if winningTeam in teamNames and losingTeam in teamNames:
        S.add(z3.Int(winningTeam + "-" + losingTeam) == 3)
        S.add(z3.Int(losingTeam + "-" + winningTeam) == 0)
    return S

def findAllScenarios(S, index):
    "Returns a list of teams which *can* satisfy predicate pos."
    # S.push()
    # enforce where SFS qualifies

    finalResults = []
    finalGames = []
    currIndex = 0

    while S.check() == z3.sat:
        # for faster loading times, return first 100 scenarios (100 * 12 teams)
        if len(finalResults) > 6:
            break
        # skip over seen scenarios until it reaches index, could be optimized here
        if currIndex < index:
            m = S.model()
            block = []
            for d in m:
                # create a constant from declaration
                c = d()
                block.append(c != m[d])
            S.add(z3.Or(block))
            currIndex += 1
            continue

        # print("SFS Position", teams[8].name, S.model()[teams[8].position])
        m = S.model()
        print(m)
        m2 = copy.deepcopy(m)
        games = {}

        for d in m.decls():
            if "_pos" in d.name():
                team = list(filter(lambda t: t.name == d.name()[0:3], teams))[0]
                    
                new_wins = 0
                new_losses = 0
                new_map_diff = 0
                currGames = {}

                # get all the games related to team
                for e in m2.decls():
                    if team.name in e.name() and "_pos" not in e.name():
                        # save result of games
                        if e.name()[4:7]+"-"+e.name()[0:3] in games:
                            games[e.name()[4:7]+"-"+e.name()[0:3]].append(int(m2[e].as_string()))
                            currGames[e.name()[4:7]+"-"+e.name()[0:3]].append(int(m2[e].as_string()))
                        else:
                            games[e.name()] = [int(m2[e].as_string())]
                            currGames[e.name()] = [int(m2[e].as_string())]

                        # if e.name()[0:3] == team.name and m2[e] == 3:
                        #     new_wins += 1
                        # elif e.name()[0:3] == team.name:
                        #     new_losses += 1
                        # games[e.name()] = m2[e]
                        # games.append(e.name() + " " + str(m2[e]))

                print(currGames)
                for key, val in currGames.items():
                    if team.name == key[0:3]:
                        if val[0] == 3:
                            new_wins += 1
                        else:
                            new_losses += 1
                        new_map_diff += val[0] - val[1]
                    else:
                        if val[1] == 3:
                            new_wins += 1
                        else:
                            new_losses += 1
                        new_map_diff += val[1] - val[0]

                finalResults.append(Scenario(team.name, int(m[d].as_string()), team.win + new_wins, team.loss + new_losses, team.diff + new_map_diff, team.region))
                currIndex += 1
                print("%s = %s" % (d.name(), m[d]), team.win + new_wins, team.loss + new_losses, team.diff + new_map_diff, team.finalMapDiff)
                    
        print("\n")
        finalGames.append(games)

        block = []
        for d in m:
            # create a constant from declaration
            c = d()
            block.append(c != m[d])
        S.add(z3.Or(block))
    
    # S.pop()
    return json.dumps(([s.__dict__ for s in finalResults],finalGames))

S = initSolver()
# S = teamWinsMatch(S, "ATL", "BOS")
print(findAllScenarios(S, 0))

# winners = findTeamsWithPossiblePosition(S, teams)

# print('Possible teams that can qualify:\n%s\n' % (
#     '\n'.join('  ' + t.name for t in winners)))

# Tools: https://www.owlstandings.com/
# https://www.cse.iitk.ac.in/users/spramod/using-smt-solvers-to-analyze-the-premier-league-table.html      
# https://www.youtube.com/watch?v=f5ygXQKF6M8