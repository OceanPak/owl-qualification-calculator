import React from "react";
import TeamImage from "./TeamImage"

class ResultsTable extends React.Component {

    getKeys = function(){
        var result = Object.keys(this.props.result[0]);
        result.push("2")
        return result
    }

    resultTableContent = function(row) {
        return <div>
            <tr class="row1">
                    <td><TeamImage team={row[0].substring(0,3)} /></td>
                    <td>{row[0].substring(0,3)}</td>
                    <td>{row[1][0]}</td>
                    <td class="resultsButtons">
                        <button type="button" onClick={() => this.props.fetch("mustWin", row[0], row[0].substring(0,3))}>
                            {row[0].substring(0,3)} wins
                        </button>
                        <button type="button" onClick={() => this.props.fetch("mustSweep", row[0], row[0].substring(0,3))}>
                            {row[0].substring(0,3)} sweeps
                        </button>
                    </td>
                </tr>
                <tr class="row2">
                    <td class="normal"><TeamImage team={row[0].substring(4,7)} /></td>
                    <td class="normal">{row[0].substring(4,7)}</td>
                    <td class="normal">{row[1][1]}</td>
                    <td class="resultsButtons">
                        <button type="button" onClick={() => this.props.fetch("mustWin", row[0], row[0].substring(4,7))}>
                            {row[0].substring(4,7)} wins
                        </button>
                        <button type="button" onClick={() => this.props.fetch("mustSweep", row[0], row[0].substring(4,7))}>
                            {row[0].substring(4,7)} sweeps
                        </button>
                    </td>
                </tr>
        </div>
    }
      
    getRowsData = function(){
        var items = this.props.result;
        if (items.length <= 1) {
            return <div>
            </div>
        }
        
        if (items.length <= 3) {
            return items.map((row, index)=>{ // 2 trs
                return <div class="post-item" style={{width: "50%"}}>
                    {this.resultTableContent(row)}
                </div>
            })
        }
        return items.map((row, index)=>{ // 2 trs
            return <div class="post-item">
                {this.resultTableContent(row)}
            </div>
        })
    }

    checkIfEmpty = function() {
        var items = this.props.result;
        if (items.length > 1) {
            return <p class="tableHeader"><b>Match Result</b></p>
        }
    }
      
    render() {
        return (
            <div class="results">
                    {this.checkIfEmpty()}
                    <div class="results-table">
                        <tbody>
                            {this.getRowsData()}
                        </tbody>
                    </div>
            </div>
        );
    }
}

export default ResultsTable;
