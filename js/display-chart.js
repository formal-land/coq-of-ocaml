const chartElement = document.getElementById('chart');
const chartProperties = window.chart;

if (chartElement && chartProperties) {
  const context = chartElement.getContext('2d');
  const colors = {
    blue: "#75caeb",
    blueBackground: "#dcf1fa",
    green: "#28b62c",
    greenBackground: "#c3f2c5",
    red: "#ff4136",
    redBackground: "#fecfcc"
  };
  const compilingLines = chartProperties.compiling[chartProperties.compiling.length - 1];
  const generatedLines = chartProperties.generated[chartProperties.generated.length - 1];
  const conversionRatio = Math.round(compilingLines / generatedLines * 100);

  new Chart(context, {
    type: 'line',
    data: {
      labels: chartProperties.labels,
      datasets: [
        {
          label: 'Compiling lines',
          backgroundColor: colors.greenBackground,
          borderColor: colors.green,
          data: chart.compiling,
          lineTension: 0
        },
        {
          label: 'Generated lines',
          backgroundColor: colors.blueBackground,
          borderColor: colors.blue,
          data: chart.generated,
          lineTension: 0
        }
      ]
    },
    options: {
      responsive: true,
      title: {
        display: true,
        fontSize: 28,
        text: `Progress towards compilation (${conversionRatio}%)`
      },
      tooltips: {
        mode: 'index',
        intersect: false,
      },
      hover: {
        mode: 'nearest',
        intersect: true
      },
      scales: {
        xAxes: [{
          display: true,
          scaleLabel: {
            display: true,
            fontSize: 16,
            labelString: 'Date (2020)'
          }
        }],
        yAxes: [{
          display: true,
          scaleLabel: {
            display: true,
            fontSize: 16,
            labelString: 'Lines'
          }
        }]
      }
    }
  });
}
