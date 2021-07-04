# Purpose: To generate all the possibilties for a given team to qualify

# Load the current W L Diff for played matches
# Calculate for the specific team, to see min score needed to qualify
# For all future matches, find all combinations that satisfy that min score

# Disregard tie breakers for now

class Team:
    def __init__(self, name, region):
        self.name = name
        self.win = 0
        self.loss = 0
        self.diff = 0
        self.region = region
        self.upcomingGames = []

# list of created teams
db = {}

# list of upcoming games

def generateWinningCombinations(teamname):
    team = db[teamname]
    
