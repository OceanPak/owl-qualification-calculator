import './App.css';
import React, { useState, useEffect } from 'react';
import ResultsTable from "./ResultsTable"

// https://www.owlstandings.com/

class NameForm extends React.Component {
  constructor(props) {
    super(props);
    this.state = {pred1: '', pred2: ''};

    this.handleChange = this.handleChange.bind(this);
    this.handleSubmit = this.handleSubmit.bind(this);
  }

  handleChange(event) {
    console.log([event.target.name]);
    this.setState({ [event.target.name] : event.target.value});
  }

  handleSubmit(event) {
    console.log(this.state);
    event.preventDefault();
  }

  render() {
    return (
      <form onSubmit={this.handleSubmit}>
        <label>
          <input type="text" name="pred1" value={this.state.pred1} onChange={this.handleChange} />
        </label>
        <label>
          <input type="text" name="pred2" value={this.state.pred2} onChange={this.handleChange} />
        </label>
        <input type="submit" value="Submit" />
      </form>
    );
  }
}

const useSortableData = (teams, config = null) => {
  const [sortConfig, setSortConfig] = useState(config);

  const sortedTeams = React.useMemo(() => {
    let sortableTeams = [...teams];
    if (sortConfig !== null) {
      sortableTeams.sort((a, b) => {
        if (a[sortConfig.key] < b[sortConfig.key]) {
          return sortConfig.direction === 'ascending' ? -1 : 1;
        }
        if (a[sortConfig.key] > b[sortConfig.key]) {
          return sortConfig.direction === 'ascending' ? 1 : -1;
        }
        return 0;
      });
    }
    return sortableTeams;
  }, [teams, sortConfig]);

  const requestSort = (key) => {
    let direction = 'ascending';
    if (
      sortConfig &&
      sortConfig.key === key &&
      sortConfig.direction === 'ascending'
    ) {
      direction = 'descending';
    }
    setSortConfig({ key, direction });
  };

  return { teams: sortedTeams, requestSort, sortConfig };
};

const TeamTable = (props) => {
  const { teams, requestSort, sortConfig } = useSortableData(props.teams);
  const getClassNamesFor = (name) => {
    if (!sortConfig) {
      return;
    }
    return sortConfig.key === name ? sortConfig.direction : undefined;
  };

  const [currentTime, setCurrentTime] = useState(0);

  useEffect(() => {
    fetch('/time').then(res => res.json()).then(data => {
      setCurrentTime(data.time);
    });
  }, []);

  var index = 0;
  const threshold = 12;
  // TODO: Do filtering here, called by onclick

  return (
    <div className="container">
      <table>
      <thead>
        <tr>
          <th>
            <button 
              type="button" 
              onClick={() => requestSort('rank')}
              className={getClassNamesFor('rank')}
            >
              Rank
            </button>
          </th>
          <th>
            <button 
              type="button" 
              onClick={() => requestSort('team')}
              className={getClassNamesFor('team')}
            >
              Team
            </button>
          </th>
          <th>
            <button 
              type="button" 
              onClick={() => requestSort('win')}
              className={getClassNamesFor('win')}
            >
              W
            </button>
          </th>
          <th>
            <button 
              type="button" 
              onClick={() => requestSort('loss')}
              className={getClassNamesFor('loss')}
            >
              L
            </button>
          </th>
          <th>
            <button 
              type="button" 
              onClick={() => requestSort('diff')}
              className={getClassNamesFor('diff')}
            >
              Diff
            </button>
          </th>
        </tr>
      </thead>
      <tbody>
        {teams.map((team) => (
          <tr key={team.team}>
            <td>{team.rank}</td>
            <td>{team.team}</td>
            <td>{team.win}</td>
            <td>{team.loss}</td>
            <td>{team.diff}</td>
          </tr>
        ))}
      </tbody>
    </table>
    <p>The current time is {currentTime}.</p>
    {/* {result.map(r => <p>{r.name}</p>)} */}
    <NameForm></NameForm>
    <StandingsTable index={index} threshold={threshold} />
    </div>
  );
}

const RenderRow = (props) =>{ // 3 tds here
  return props.keys.map((key, index)=>{
      return <td>{props.data[key]}</td>
  })
}

class StandingsTable extends React.Component {
  constructor(props){
    super(props);
    this.threshold = this.props.threshold
    this.getHeader = this.getHeader.bind(this);
    this.getRowsData = this.getRowsData.bind(this);
    this.getKeys = this.getKeys.bind(this);
    this.state = {
      batchIndex: this.props.index,
      index: this.props.index,
      fullData: [ {} ],
      data: [ {} ],
      result : [ {} ],
      sortKey: "pos",
      sortAscending: true,
      conditions: {index: 0, mustQualify: [], mustWin: {}, mustSweep: {}}
    }
    console.log(this.state)
  }

  componentDidMount() {
    fetch('/solve').then(res => res.json()).then(data => {
      console.log(data)
      // save all the data for index filtering
      this.setState({fullData: data})

      // TODO: save this result in the state of the parent
      
      // filter based on index
      var filteredData = data[0].filter((_, index) => index >= this.state.index * this.threshold && index < this.state.index * this.threshold + this.threshold)
      filteredData.sort((a,b) => {
        if (a["pos"] < b["pos"]) {
          return -1
        } else {
          return 1
        }
      })
      
      var filteredResult = [data[1][this.state.index]] // TODO: Should have index

      // fix keys to fit the format of the table
      filteredResult.map(obj => filteredResult = Object.keys(obj).map(function (key) { return [key, obj[key]]} ))
      
      // set to state
      this.setState({data: filteredData, result: filteredResult})
      console.log("state", this.state)
    });
  }

  nextScenario = function() {
    var newIndex = this.state.index + 1

    if (newIndex * this.threshold >= this.state.fullData[0].length) {
      this.setState({index: 0, batchIndex: this.state.batchIndex + newIndex})

      fetch("/solve-next-batch", {
        method: "POST",
        headers: {
        'Content-Type' : 'application/json'
        },
        body: JSON.stringify(newIndex)
      }).then(res => res.json()).then(data => {
        // save all the data for index filtering
        this.setState({fullData: data})

        newIndex = 0
        
        // filter based on index
        var filteredData = data[0].filter((_, index) => index >= newIndex * this.threshold && index < newIndex * this.threshold + this.threshold)
        filteredData.sort((a,b) => {
          if (a["pos"] < b["pos"]) {
            return -1
          } else {
            return 1
          }
        })

        var filteredResult = [data[1][newIndex]] // TODO: Should have index
  
        // fix keys to fit the format of the table
        filteredResult.map(obj => filteredResult = Object.keys(obj).map(function (key) { return [key, obj[key]]} ))
        
        // set to state
        this.setState({data: filteredData, result: filteredResult})
        console.log("new state", this.state)
      });
    } else {
      this.setState({index: newIndex})
      // filter based on index
      var filteredData = this.state.fullData[0].filter((_, index) => index >= newIndex * this.threshold && index < newIndex * this.threshold + this.threshold)
      filteredData.sort((a,b) => {
        if (a["pos"] < b["pos"]) {
          return -1
        } else {
          return 1
        }
      })
      
      var filteredResult = [this.state.fullData[1][newIndex]] // TODO: Should have index
      
      // fix keys to fit the format of the table
      filteredResult.map(obj => filteredResult = Object.keys(obj).map(function (key) { return [key, obj[key]]} ))
      
      // set to state
      this.setState({data: filteredData, result: filteredResult})
      console.log("full state", this.state)
    }
  }
  
  getKeys = function(){
    var keys = Object.keys(this.state.data[0]);
    // switching pos and name so pos goes first
    if (keys.length > 1) {
      var temp = keys[1]
      keys[1] = keys[0]
      keys[0] = temp
      return keys
    }
    return keys;
  }

  sortByKey = function(key) {
    let sortableTeams = [...this.state.data];
    // console.log(sortableTeams)
    sortableTeams.sort((a,b) => {
      if (key == this.state.sortKey) {
        let reverse = !this.state.sortAscending
        this.setState({sortAscending: reverse})
        if (reverse) {
          if (a[key] < b[key]) {
            return -1
          } 
          if (a[key] > b[key]) {
            return 1
          }
          return 0;
        } else {
          if (a[key] < b[key]) {
            return 1
          } 
          if (a[key] > b[key]) {
            return -1
          }
          return 0;
        }
      } else {
        this.setState({sortKey: key, sortAscending: true})
        if (a[key] < b[key]) {
          return -1
        } 
        if (a[key] > b[key]) {
          return 1
        }
        return 0;
      }
    })
    this.setState({data: sortableTeams})
  }
  
  getHeader = function(){
    var keys = this.getKeys();
    return keys.map((key, index)=>{
      return <th>
        <button type="button" onClick={() => this.sortByKey(key)}>
          {key.toUpperCase()}</button></th>
    })
  }
  
  getRowsData = function(){
    var items = this.state.data;
    var keys = this.getKeys();
    return items.map((row, index)=>{
      return <tr><RenderRow data={row} keys={keys}/>
      <button 
        type="button" 
        onClick={() => this.fetchConditions("mustQualify", "", row.name)}
      >
        {row.name} must qualify
      </button></tr>
    })
  }

  fetchConditions = (condition, matchName, winningTeam) => {
    console.log(this.state)
    var newstate = this.state.conditions
    if (condition == "mustQualify") {
      newstate[condition].push(winningTeam)
    } else {
      newstate[condition][matchName] = winningTeam
    }
    console.log("new state", newstate)
    // this.setState({conditions: newstate})
    fetch("/solve_conditions", {
        method: "POST",
        headers: {
        'Content-Type' : 'application/json'
        },
        body: JSON.stringify(newstate)
    }).then(res => res.json()).then(data => {
      // save all the data for index filtering
      console.log("all data", data) // TODO: When there are no cases
      this.setState({fullData: data})

      let newIndex = 0
      this.setState({index: newIndex, batchIndex: newIndex})
      
      // filter based on index
      if (data[0].length > 0) {
        var filteredData = data[0].filter((_, index) => index >= newIndex * this.threshold && index < newIndex * this.threshold + this.threshold)
        filteredData.sort((a,b) => {
          if (a["pos"] < b["pos"]) {
            return -1
          } else {
            return 1
          }
        })
      } else {
        var filteredData = [ {}, {} ]
      }

      if (data[1].length > 0) {
        var filteredResult = [data[1][newIndex]] // TODO: Should have index
        console.log(filteredResult)
      } else {
        var filteredResult = [ {}, {} ]
      }
      
      // fix keys to fit the format of the table
      filteredResult.map(obj => filteredResult = Object.keys(obj).map(function (key) { return [key, obj[key]]} ))
      
      // set to state
      this.setState({data: filteredData, result: filteredResult})
      console.log("new state", this.state)
    });
    
  }

  checkIfEmpty = function(length){
    if (length == 2) {
      return <p>No situations found!</p>
    } else {
      return <div class="data">
          <div class="placing">
            <table>
              <thead>
                <tr>{this.getHeader()}</tr>
              </thead>
              <tbody>
                {this.getRowsData()}
              </tbody>
            </table>
          </div>
          <ResultsTable result={this.state.result} fetch={this.fetchConditions}/>
      </div>
    }
  }

  buttonIfEmpty = function(length){
    if (length == 2) {
      return <button 
        type="button" 
        onClick={() => window.location.reload()}
      >
        Reset Search
      </button>
    } else {
      return <button 
        type="button" 
        onClick={() => this.nextScenario()}
      >
        Next Scenario
      </button>
    }
  }

  displayEnforcedWinConditions = function(conditions) {
    return Object.entries(conditions).map((arr) => {
      return <p>{arr[1]} wins {arr[0]}</p>
    })
  }

  displayEnforcedSweepConditions = function(conditions) {
    return Object.entries(conditions).map((arr) => {
      return <p>{arr[1]} sweeps {arr[0]}</p>
    })
  }

  displayEnforcedQualifyConditions = function(conditions) {
    return conditions.map((team) => {
      return <p>{team} qualifies</p>
    })
  }
  
  render() {
    return (
      <div>
        {this.checkIfEmpty(this.state.data.length)}
        {this.buttonIfEmpty(this.state.data.length)}
        <p>Enforced Conditions: 
          {this.displayEnforcedWinConditions(this.state.conditions["mustWin"])}
          {this.displayEnforcedSweepConditions(this.state.conditions["mustSweep"])}
          {this.displayEnforcedQualifyConditions(this.state.conditions["mustQualify"])}</p>
      </div>
    );
  }
}

function App() {
  var index = 0;
  const threshold = 12;
  return (
    <div className="App">
      <StandingsTable index={index} threshold={threshold} />
    </div>
  )
}

export default App;