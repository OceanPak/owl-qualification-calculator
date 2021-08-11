import time
from flask import Flask
from z3_test import initSolver, findTeamsWithPossiblePosition

app = Flask(__name__)

@app.route('/time')
def get_current_time():
    return {'time': time.time()}

@app.route('/solve')
def get_winning_scenarios():
    S = initSolver()
    findTeamsWithPossiblePosition(S)
    return "hello"