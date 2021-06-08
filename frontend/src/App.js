import './App.css';
import React from 'react';

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

function App() {
  const teams = [
    {rank: 1, team: 'dragons', win: 3, loss: 1, diff: 3},
    {rank: 2, team: 'dynasty', win: 2, loss: 1, diff: 1}
  ]
  const [sortedField, setSortedField] = React.useState(null);
  let sortedProducts = [...teams];
  if (sortedField !== null) {
    sortedProducts.sort((a, b) => {
      if (a[sortedField] < b[sortedField]) {
        return -1;
      }
      if (a[sortedField] > b[sortedField]) {
        return 1;
      }
      return 0;
    });
  }
  return (
    <div className="ree">
      <table>
      <thead>
        <tr>
          <th>
            <button type="button" onClick={() => setSortedField('rank')}>
              Rank
            </button>
          </th>
          <th>
            <button type="button" onClick={() => setSortedField('team')}>
              Team
            </button>
          </th>
          <th>
            <button type="button" onClick={() => setSortedField('win')}>
              W
            </button>
          </th>
          <th>
            <button type="button" onClick={() => setSortedField('loss')}>
              L
            </button>
          </th>
          <th>
            <button type="button" onClick={() => setSortedField('diff')}>
              Diff
            </button>
          </th>
        </tr>
      </thead>
      <tbody>
        {teams.map(team => (
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
    <NameForm></NameForm>
    </div>
  );
}

export default App;
