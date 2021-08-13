import time
from flask import Flask
from z3_calc import initSolver, findAllScenarios

app = Flask(__name__)

@app.route('/time')
def get_current_time():
    return {'time': time.time()}

@app.route('/solve')
def get_winning_scenarios():
    S = initSolver()
    return findAllScenarios(S, 0)