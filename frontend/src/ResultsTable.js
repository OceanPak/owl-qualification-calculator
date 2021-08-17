import React from "react";
import TeamImage from "./TeamImage"

class ResultsTable extends React.Component {

    getKeys = function(){
        var result = Object.keys(this.props.result[0]);
        result.push("2")
        return result
    }
      
    getRowsData = function(){
        var items = this.props.result;
        if (items.length <= 1) {
            return <div>
            </div>
        }
        
        return items.map((row, index)=>{ // 2 trs
            return <div>
                <tr class="row1">
                    <td><TeamImage team={row[0].substring(0,3)} /></td>
                    <td>{row[0].substring(0,3)}</td>
                    <td>{row[1][0]}</td>
                    <td>
                        <button type="button" onClick={() => this.props.fetch("mustWin", row[0], row[0].substring(0,3))}>
                            Should Win
                        </button>
                        <button type="button" onClick={() => this.props.fetch("mustSweep", row[0], row[0].substring(0,3))}>
                            Should Sweep
                        </button>
                    </td>
                </tr>
                <tr class="row2">
                    <td><TeamImage team={row[0].substring(4,7)} /></td>
                    <td>{row[0].substring(4,7)}</td>
                    <td>{row[1][1]}</td>
                    <td>
                        <button type="button" onClick={() => this.props.fetch("mustWin", row[0], row[0].substring(4,7))}>
                            Should Win
                        </button>
                        <button type="button" onClick={() => this.props.fetch("mustSweep", row[0], row[0].substring(4,7))}>
                            Should Sweep
                        </button>
                    </td>
                </tr>
                </div>
        })
    }

    checkIfEmpty = function() {
        var items = this.props.result;
        if (items.length > 1) {
            return <tr>
            <th>Match Result</th>
            </tr>
        }
    }
      
    render() {
        return (
            <div class="results">
                <table>
                    {this.checkIfEmpty()}
                    <tbody>
                        {this.getRowsData()}
                    </tbody>
                </table>
            </div>
        );
    }
}

export default ResultsTable;
