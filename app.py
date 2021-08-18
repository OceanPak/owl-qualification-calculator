import time
from flask import Flask, request
from z3_calc import initSolver, findAllScenarios, teamMustQualify, teamWinsMatch, teamSweepMatch

app = Flask(__name__)

@app.route('/solve', methods=['POST'])
def get_winning_scenarios():
    # handle the POST request
    if request.method == 'POST':
        region = request.get_json()
        if region != "WEST" and region != "EAST":
            return "Error: Non supported region"
        S = initSolver(region)
        return findAllScenarios(S, 0)
    else:
        return "Only POST request accepted"

@app.route('/solve-next-batch', methods=['POST'])
def get_winning_scenarios_index():
    # handle the POST request
    if request.method == 'POST':
        received = request.get_json()
        index = received["index"]
        if index < 0:
            return "Error: Index cannot be negative"
        region = received["region"]
        if region != "WEST" and region != "EAST":
            return "Error: Non supported region"
        S = initSolver(region)
        return findAllScenarios(S, index)
    else:
        return "Only POST request accepted"

@app.route('/solve_conditions', methods=['POST'])
def get_winning_scenarios_all_conditions():
    # handle the POST request
    if request.method == 'POST':
        team = request.get_json()
        region = team["region"]
        if region != "WEST" and region != "EAST":
            return "Error: Non supported region"
        S = initSolver(region)
        if team["mustQualify"] != []:
            for t in team["mustQualify"]:
                S = teamMustQualify(S, t)

        if team["mustWin"] != {}:
            for matchName, winTeam in team["mustWin"].items():
                if matchName[0:3] == winTeam:
                    S = teamWinsMatch(S, winTeam, matchName[4:7])
                elif matchName[4:7] == winTeam:
                    S = teamWinsMatch(S, winTeam, matchName[0:3])

        if team["mustSweep"] != {}:
            for matchName, winTeam in team["mustSweep"].items():
                if matchName[0:3] == winTeam:
                    S = teamSweepMatch(S, winTeam, matchName[4:7])
                elif matchName[4:7] == winTeam:
                    S = teamSweepMatch(S, winTeam, matchName[0:3])

        index = team["index"]
        if index < 0:
            return "Error: Index cannot be negative"

        return findAllScenarios(S, index)
    else:
        return "Only POST request accepted"