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
      data: [
        { }
      ],
      result : [ {} ]
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
      var filteredResult = [data[1][this.state.index]] // TODO: Should have index

      // fix keys to fit the format of the table
      filteredResult.map(obj => filteredResult = Object.keys(obj).map(function (key) { return [key, obj[key]]} ))
      
      // set to state
      this.setState({data: filteredData, result: filteredResult})
      console.log("state", this.state.result)
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
      var filteredResult = [this.state.fullData[1][newIndex]] // TODO: Should have index
      
      // fix keys to fit the format of the table
      filteredResult.map(obj => filteredResult = Object.keys(obj).map(function (key) { return [key, obj[key]]} ))
      
      // set to state
      this.setState({data: filteredData, result: filteredResult})
      console.log("full state", this.state)
    }
  }
  
  getKeys = function(){
    return Object.keys(this.state.data[0]);
  }
  
  getHeader = function(){
    var keys = this.getKeys();
    return keys.map((key, index)=>{
      return <th>{key.toUpperCase()}</th>
    })
  }
  
  getRowsData = function(){
    var items = this.state.data;
    var keys = this.getKeys();
    return items.map((row, index)=>{
      return <tr><RenderRow data={row} keys={keys}/></tr>
    })
  }
  
  render() {
    return (
      <div>
        <div class="data">
          <div>
            <table>
              <thead>
                <tr>{this.getHeader()}</tr>
              </thead>
              <tbody>
                {this.getRowsData()}
              </tbody>
            </table>
          </div>
          <ResultsTable result={this.state.result} />
        </div>
        <button 
          type="button" 
          onClick={() => this.nextScenario()}
        >
          Next Scenario
        </button>
      </div>
    );
  }
}

function App() {
  return (
    <div className="App">
      <TeamTable
        teams={[
          {rank: 1, team: 'dragons', win: 18, loss: 4, diff: 16},
          {rank: 2, team: 'dynasty', win: 11, loss: 3, diff: 18},
          {rank: 3, team: 'fusion', win: 9, loss: 5, diff: 12},
          {rank: 4, team: 'hunters', win: 9, loss: 5, diff: 7},
          {rank: 5, team: 'spark', win: 7, loss: 7, diff: 4},
          {rank: 6, team: 'excelsior', win: 7, loss: 7, diff: 1},
          {rank: 7, team: 'charge', win: 3, loss: 9, diff: -18},
          {rank: 8, team: 'valiant', win: 0, loss: 14, diff: -40},
        ]}
      />
    </div>
  )
}

export default App;