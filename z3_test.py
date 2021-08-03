import z3, copy

S = z3.Solver()

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

upcoming_games = [
    Game("ATL", "BOS"),
    Game("TOR", "DAL"),
    Game("WAS", "GLA")
]

gameVars = []

# Encode constraints on the number of points that can be scored in each game
for g in upcoming_games:
    g.team1score = z3.Int(g.team1 + "-" + g.team2)
    g.team2score = z3.Int(g.team2 + "-" + g.team1)
    gameVars.append(g.team1score)
    gameVars.append(g.team2score)
    S.add(g.team1score >= 0)
    S.add(g.team1score <= 3)
    S.add(g.team2score >= 0)
    S.add(g.team2score <= 3)
    S.add(g.team1score + g.team2score <= 5)
    S.add(z3.Or(g.team1score == 3, g.team2score == 3))

# Figure out the points tally and score at the end of the stage

allTeams = [
    Team("BOS", 3, 0, 8, "WEST"),
    Team("DAL", 3, 0, 5, "WEST"),
    Team("PAR", 3, 1, 4, "WEST"),
    Team("ATL", 2, 1, 5, "WEST"),
    Team("GLA", 2, 1, 3, "WEST"),
    Team("WAS", 2, 1, 3, "WEST"),
    Team("TOR", 2, 1, 1, "WEST"),
    Team("HOU", 2, 2, -1, "WEST"),
    Team("SFS", 2, 2, 0, "WEST"),
    Team("LDN", 0, 4, -9, "WEST"),
    Team("FLA", 0, 4, -8, "WEST"),
    Team("VAN", 0, 4, -11, "WEST")
]

teams = allTeams

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

def findTeamsWithPossiblePosition(S, table):
    "Returns a list of teams which *can* satisfy predicate pos."
    teams = []

    # S.push()
    # enforce where SFS qualifies
    sfs_lst = list(filter(lambda t: t.name == "SFS", table))
    S.add(sfs_lst[0].position <= 6)
    
    while S.check() == z3.sat:
        print("SFS Position", allTeams[8].name, S.model()[allTeams[8].position])
        m = S.model()
        m2 = copy.deepcopy(m)
            
        for d in m.decls():
            if "_pos" in d.name():
                teamName = d.name()[0:3]
                    
                games = []
                for e in m2.decls():
                    if teamName in e.name() and "_pos" not in e.name():
                        games.append(e.name() + " " + str(m2[e]))
                    
                print("%s = %s" % (d.name(), m[d]), games)
                    
        print("\n")

        block = []
        for d in m:
            # create a constant from declaration
            c = d()
            block.append(c != m[d])
        S.add(z3.Or(block))
    
    # S.pop()
    return teams

    # for t in table:
    #     S.push()
    #     # S.add(t.position <= 6) # only 10 teams that qualify, so only ten sats

    #     if S.check() == z3.sat:
    #         # if S.check() == z3.sat:
    #         print("SFS Position", allTeams[8].name, S.model()[allTeams[8].position])
    #         m = S.model()
    #         m2 = copy.deepcopy(m)
            
    #         for d in m.decls():
    #             if "_pos" in d.name():
    #                 # print("%s = %s" % (d.name(), m[d]))
    #                 teamName = d.name()[0:3]
    #                 # print("teamName", teamName)
                    
    #                 games = []
    #                 for e in m2.decls():
    #                     # print(e.name())
    #                     # print(teamName in e.name())
    #                     if teamName in e.name() and "_pos" not in e.name():
    #                         games.append(e.name() + " " + str(m2[e]))
    #                         # print("%s = %s" % (e.name(), m2[e]))
                    
    #                 print("%s = %s" % (d.name(), m[d]), games)
                    
    #         teams.append(t)
    #         print("\n")

    #         # S.add(m.decls() != S.model().decls())

    #     S.pop()
    # return teams

winners = findTeamsWithPossiblePosition(S, teams)
# print('Possible teams that can qualify:\n%s\n' % (
#     '\n'.join('  ' + t.name for t in winners)))

# Tools: https://www.owlstandings.com/
# https://www.cse.iitk.ac.in/users/spramod/using-smt-solvers-to-analyze-the-premier-league-table.html      
# https://www.youtube.com/watch?v=f5ygXQKF6M8