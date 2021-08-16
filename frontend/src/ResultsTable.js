import React from "react";
import RenderRow from "./RenderRow"

class ResultsTable extends React.Component {

    getKeys = function(){
        return Object.keys(this.props.result[0]);
    }
      
    getRowsData = function(){
        var items = this.props.result;
        var keys = this.getKeys();
        return items.map((row, index)=>{ // 2 trs
            return <tr key={index}><RenderRow key={index} data={row} keys={keys}/></tr>
        })
    }
      
    render() {
        return (
            <div>
                <table>
                    <tbody>
                        {this.getRowsData()}
                    </tbody>
                </table>
            </div>
        );
    }
}

export default ResultsTable;
