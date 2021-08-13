import './App.css';
import React, { useState, useEffect } from 'react';

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

  // const initialValue = [
  //   { name: "", pos: "", games: {}, wins: 0, loss: 0, diff: 0, region: "" }];

  // const [result, setResult] = useState(initialValue);

  // useEffect(() => {
  //   fetch('/solve').then(res => res.json()).then(data => {
  //     console.log(data)
  //     setResult(data);
  //   });
  // }, []);

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
    <Table />
    </div>
  );
}

class Table extends React.Component {
  constructor(props){
    super(props);
    // console.log("bla")
    // console.log(props)
    this.getHeader = this.getHeader.bind(this);
    this.getRowsData = this.getRowsData.bind(this);
    this.getKeys = this.getKeys.bind(this);
    this.state = {
      data: [
        { }
      ]
    }
  }

  componentDidMount() {
    fetch('/solve').then(res => res.json()).then(data => {
      data.map(obj => obj.games = Object.keys(obj.games).map(function (key) { return [key, obj.games[key]]} ))
      console.log("before", data)
      this.setState({data: data})
      console.log("state", this.state.data)
    });
  }
  
  getKeys = function(){
    return Object.keys(this.state.data[0]);
  }
  
  getHeader = function(){
    var keys = this.getKeys();
    return keys.map((key, index)=>{
      return <th key={key}>{key.toUpperCase()}</th>
    })
  }
  
  getRowsData = function(){
    var items = this.state.data;
    var keys = this.getKeys();
    return items.map((row, index)=>{
      return <tr key={index}><RenderRow key={index} data={row} keys={keys}/></tr>
    })
  }
  
  render() {
    return (
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
    );
  }
 }
 
 const RenderRow = (props) =>{
  return props.keys.map((key, index)=>{
      return <td key={props.data[key]}>{props.data[key]}</td>
  })
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