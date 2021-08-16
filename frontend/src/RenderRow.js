const RenderRow = (props) =>{ // 3 tds here
    return props.keys.map((key, index)=>{
        return <td key={props.data[key]}>{props.data[key]}</td>
    })
}

export default RenderRow;