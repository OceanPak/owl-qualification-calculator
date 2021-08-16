import time
from flask import Flask, request
from z3_calc import initSolver, findAllScenarios

app = Flask(__name__)

@app.route('/time')
def get_current_time():
    return {'time': time.time()}

@app.route('/solve')
def get_winning_scenarios():
    S = initSolver()
    return findAllScenarios(S, 0)

@app.route('/solve-next-batch', methods=['POST'])
def get_winning_scenarios_index():
    # handle the POST request
    if request.method == 'POST':
        index = request.get_json()
        if index < 0:
            return "Error: Index cannot be negative"
        S = initSolver()
        return findAllScenarios(S, index)
    else:
        return "Only POST request accepted"